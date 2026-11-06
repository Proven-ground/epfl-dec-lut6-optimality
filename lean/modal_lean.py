"""Build, solve and certify the Lean proof on Modal. Nothing runs on the launching machine.

One app, one image, one volume:
  - the image holds elan with the pinned Lean toolchain and CaDiCaL built from the pinned commit; Modal
    caches it, so edits to the proof never rebuild it;
  - the volume holds the project with Mathlib's prebuilt oleans (fetched once with `lake exe cache get`)
    and every build product, so a rebuild recompiles only the modules whose sources changed;
  - sources are sent as function arguments (a few hundred kilobytes), never baked into the image.

Steps (`--step`):
  build     write the sources, fetch Mathlib's cache if absent, `lake build` the proof modules in parallel
  emit      `lake exe emit`: write the formula as DIMACS with Lean's own writer, report its SHA-256
  solve     CaDiCaL `--lrat --binary=false` on that DIMACS; the refutation is cached by the formula's hash
  certify   `lake build DecoderOptimality.Main`: Lean checks the refutation and prints the theorem's axioms
  all       the four in order, stopping at the first failure

    python -m modal run lean/modal_lean.py --step build
    python -m modal run lean/modal_lean.py --step build --targets DecoderOptimality.Bridge,DecoderOptimality.Structure

Cost shape, at Modal's list prices ($0.0000131 per core-second, $0.00000222 per GiB-second): a build on 8
cores and 32 GiB for 10 minutes is $0.06 CPU + $0.04 memory; the one-time Mathlib fetch on 2 cores is about
$0.03; a CaDiCaL hour on half a core and 8 GiB is $0.02 + $0.06.
"""
import hashlib
import json
import sys
import time
from pathlib import Path

import modal

LEAN_TOOLCHAIN = 'leanprover/lean4:v4.35.0'
CADICAL_COMMIT = 'c60730422e758ef1cebe7aeddf2dda31c996bf04'  # rel-3.0.1, the solver of the paper's evidence
HERE = Path(__file__).resolve().parent
PROJECT = '/vol/project'

app = modal.App('proving-ground-lean')
image = (
    modal.Image.debian_slim(python_version='3.11')
    .apt_install('git', 'curl', 'build-essential', 'ca-certificates')
    .run_commands(
        'curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh'
        f' | sh -s -- -y --default-toolchain {LEAN_TOOLCHAIN}',
        'git clone https://github.com/arminbiere/cadical /opt/cadical',
        f'cd /opt/cadical && git checkout {CADICAL_COMMIT} && ./configure && make -j4',
    )
    .env({'PATH': '/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin'})
)
volume = modal.Volume.from_name('proving-ground-lean', create_if_missing=True)


def sources() -> dict:
    """Project sources relative to the project root, excluding build products."""
    files = {}
    for path in sorted(HERE.rglob('*')):
        if not path.is_file() or '.lake' in path.parts or path.suffix in ('.py', '.pyc'):
            continue
        if path.suffix not in ('.lean', '.toml') and path.name not in ('lean-toolchain', 'lake-manifest.json'):
            continue
        files[path.relative_to(HERE).as_posix()] = path.read_text(encoding='utf-8')
    return files


def run(cmd, cwd=PROJECT, timeout=None):
    import subprocess
    started = time.monotonic()
    proc = subprocess.run(cmd, cwd=cwd, shell=isinstance(cmd, str), capture_output=True, text=True,
                          timeout=timeout)
    return {'cmd': cmd if isinstance(cmd, str) else ' '.join(cmd), 'exit': proc.returncode,
            'seconds': round(time.monotonic() - started, 1), 'stdout': proc.stdout, 'stderr': proc.stderr}


def write_sources(files: dict):
    root = Path(PROJECT)
    root.mkdir(parents=True, exist_ok=True)
    changed = []
    for rel, text in files.items():
        target = root / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists() or target.read_text(encoding='utf-8') != text:
            target.write_text(text, encoding='utf-8', newline='\n')
            changed.append(rel)
    return changed


def ensure_mathlib():
    """Clone Mathlib and fetch its prebuilt oleans once; later calls return at once."""
    root = Path(PROJECT)
    log = []
    if not (root / 'lake-manifest.json').exists() or not (root / '.lake' / 'packages' / 'mathlib').exists():
        log.append(run('lake update', timeout=3600))
        if log[-1]['exit'] != 0:
            return log
    marker = root / '.lake' / 'mathlib-cache-ok'
    if not marker.exists():
        log.append(run('lake exe cache get', timeout=3600))
        if log[-1]['exit'] == 0:
            marker.write_text('ok')
    return log


@app.function(image=image, cpu=8, memory=32768, timeout=7200, volumes={'/vol': volume})
def build(files: dict, targets: list) -> dict:
    changed = write_sources(files)
    log = ensure_mathlib()
    if log and log[-1]['exit'] != 0:
        volume.commit()
        return {'step': 'build', 'ok': False, 'changed': changed, 'log': log}
    log.append(run(['lake', 'build', *targets], timeout=7000))
    volume.commit()
    return {'step': 'build', 'ok': log[-1]['exit'] == 0, 'changed': changed, 'log': log}


@app.function(image=image, cpu=4, memory=16384, timeout=3600, volumes={'/vol': volume})
def emit() -> dict:
    log = [run(['lake', 'build', 'emit'], timeout=3000)]
    if log[-1]['exit'] != 0:
        return {'step': 'emit', 'ok': False, 'log': log}
    cnf = Path(PROJECT) / 'bound.cnf'
    log.append(run(['lake', 'exe', 'emit', str(cnf)], timeout=3000))
    ok = log[-1]['exit'] == 0 and cnf.exists()
    record = {'step': 'emit', 'ok': ok, 'log': log}
    if ok:
        data = cnf.read_bytes()
        header = data.split(b'\n', 1)[0].decode()
        record.update({'header': header, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()})
        (Path(PROJECT) / 'bound.cnf.sha256').write_text(record['sha256'])
    volume.commit()
    return record


@app.function(image=image, cpu=1, memory=(8192, 32768), timeout=86400, volumes={'/vol': volume})
def solve() -> dict:
    root = Path(PROJECT)
    cnf, lrat, meta = root / 'bound.cnf', root / 'bound.lrat', root / 'bound.lrat.json'
    if not cnf.exists():
        return {'step': 'solve', 'ok': False, 'error': 'bound.cnf missing: run emit first'}
    sha = hashlib.sha256(cnf.read_bytes()).hexdigest()
    if lrat.exists() and meta.exists():
        cached = json.loads(meta.read_text())
        if cached.get('cnf_sha256') == sha and cached.get('answer') == 'UNSATISFIABLE':
            return {**cached, 'step': 'solve', 'ok': True, 'cached': True}
    started = time.monotonic()
    log = run(['/opt/cadical/build/cadical', '-q', '--lrat', '--binary=false', str(cnf), str(lrat)], timeout=86000)
    answer = {20: 'UNSATISFIABLE', 10: 'SATISFIABLE'}.get(log['exit'], 'ERROR')
    record = {'step': 'solve', 'answer': answer, 'cnf_sha256': sha, 'solve_seconds': round(time.monotonic() - started, 1),
              'cadical_commit': CADICAL_COMMIT, 'exit': log['exit'], 'tail': (log['stdout'] + log['stderr'])[-800:]}
    if answer == 'UNSATISFIABLE' and lrat.exists():
        data = lrat.read_bytes()
        record.update({'lrat_bytes': len(data), 'lrat_sha256': hashlib.sha256(data).hexdigest(), 'ok': True})
        meta.write_text(json.dumps(record, indent=1))
    else:
        record['ok'] = False
    volume.commit()
    return record


@app.function(image=image, cpu=8, memory=65536, timeout=14400, volumes={'/vol': volume})
def certify(files: dict) -> dict:
    changed = write_sources(files)
    root = Path(PROJECT)
    if not (root / 'bound.lrat').exists():
        return {'step': 'certify', 'ok': False, 'error': 'bound.lrat missing: run solve first'}
    log = [run(['lake', 'build', 'DecoderOptimality.Main'], timeout=14000)]
    volume.commit()
    text = log[-1]['stdout'] + log[-1]['stderr']
    axioms = [line for line in text.splitlines() if 'depends on axioms' in line or 'axiom' in line.lower()]
    return {'step': 'certify', 'ok': log[-1]['exit'] == 0, 'changed': changed, 'axioms': axioms, 'log': log}


def show(result: dict):
    brief = {k: v for k, v in result.items() if k != 'log'}
    print(json.dumps(brief, indent=1))
    for entry in result.get('log', []):
        print(f"$ {entry['cmd']}  [exit {entry['exit']}, {entry['seconds']} s]")
        text = (entry['stdout'] + entry['stderr']).strip()
        if entry['cmd'].startswith('lake build'):
            noise = ('trace:', '✔', 'info: downloading', 'info: installing', 'Note: This linter',
                     'Hint:', '  [apply]')
            lines = [l for l in text.splitlines()
                     if not l.startswith(noise) and 'module system' not in l and l.strip()]
            print('\n'.join(lines)[-60000:])
        elif entry['exit'] != 0:
            print(text[-20000:])
        else:
            print(text[-2000:])


@app.local_entrypoint()
def main(step: str = 'build', targets: str = ''):
    files = sources()
    wanted = [t for t in targets.split(',') if t] or [
        'DecoderOptimality.Structure', 'DecoderOptimality.Bridge', 'emit']
    steps = ['build', 'emit', 'solve', 'certify'] if step == 'all' else [step]
    for s in steps:
        if s == 'build':
            result = build.remote(files, wanted)
        elif s == 'emit':
            result = emit.remote()
        elif s == 'solve':
            result = solve.remote()
        elif s == 'certify':
            result = certify.remote(files)
        else:
            raise SystemExit(f'unknown step {s}')
        show(result)
        if not result.get('ok'):
            raise SystemExit(f'step {s} failed')
