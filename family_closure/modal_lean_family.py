"""Check the family lifting lemma against the existing proof cache on Modal."""
import json
from pathlib import Path

import modal

HERE = Path(__file__).resolve().parent
app = modal.App('proven-ground-family-lean')
image = (
    modal.Image.debian_slim(python_version='3.11')
    .apt_install('git', 'curl', 'build-essential', 'ca-certificates')
    .run_commands(
        'curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh'
        ' | sh -s -- -y --default-toolchain leanprover/lean4:v4.35.0',
        'git clone https://github.com/arminbiere/cadical /opt/cadical',
        'cd /opt/cadical && git checkout c60730422e758ef1cebe7aeddf2dda31c996bf04 && ./configure && make -j4',
    )
    .env({'PATH': '/root/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin'})
    .run_commands('/root/.elan/bin/lean --version')
)
legacy_volume = modal.Volume.from_name('proving-ground-lean')
results_volume = modal.Volume.from_name('proven-ground-decoder-family-closure')


@app.function(image=image, cpu=2, memory=(4096, 8192), timeout=600,
              nonpreemptible=True, retries=0, volumes={'/vol': legacy_volume, '/results': results_volume})
def check(source: str, seconds: int = 90):
    import hashlib
    import os
    import subprocess
    import time

    root = Path('/vol/project')
    compiled = root / '.lake/build/lib/lean'
    if not (compiled / 'DecoderOptimality/Main.olean').exists():
        return {'ok': False, 'error': 'existing compiled proof is absent; no original files modified'}
    digest = hashlib.sha256(source.encode()).hexdigest()
    folder = Path('/results') / ('lean_family_' + digest[:16])
    folder.mkdir(exist_ok=True)
    target = folder / 'GenericLift.lean'
    target.write_text(source, encoding='utf-8')
    env = dict(os.environ)
    paths = [compiled]
    paths += sorted(path for path in (root / '.lake/packages').glob('*/.lake/build/lib/lean') if path.is_dir())
    env['LEAN_PATH'] = ':'.join(str(path) for path in paths)
    command = ['/root/.elan/bin/lean', '-o', str(folder / 'GenericLift.olean'), str(target)]
    start = time.monotonic()
    log = folder / 'compiler.log'
    with log.open('w') as output:
        try:
            result = subprocess.run(command, cwd=folder, env=env, stdout=output,
                                    stderr=subprocess.STDOUT, timeout=seconds)
            record = dict(ok=result.returncode == 0, exit=result.returncode,
                          command=command, source_sha256=digest,
                          seconds=round(time.monotonic() - start, 3))
        except subprocess.TimeoutExpired:
            record = dict(ok=False, error='compiler timeout', command=command,
                          source_sha256=digest, seconds=round(time.monotonic() - start, 3))
    record['stdout'] = log.read_text(encoding='utf-8')
    record['original_module_bytes'] = {name: (compiled / f'DecoderOptimality/{name}.olean').stat().st_size
                                        for name in ('Model', 'Reduced', 'Main', 'Certificate')}
    record['original_modules'] = {}
    for name in ('Model', 'Reduced', 'Structure', 'Dominance', 'Bridge', 'Certificate', 'Main'):
        path = compiled / f'DecoderOptimality/{name}.olean'
        record['original_modules'][name] = hashlib.sha256(path.read_bytes()).hexdigest()
    (folder / 'result.json').write_text(json.dumps(record, indent=2))
    results_volume.commit()
    return record


@app.local_entrypoint()
def main(diagnostic: bool = False, seconds: int = 90):
    source = ('import DecoderOptimality.Main\n#check DecoderOptimality.lowerBound\n'
              if diagnostic else (HERE / 'GenericLift.lean').read_bytes().decode('utf-8'))
    result = check.remote(source, seconds)
    (HERE / ('results/lean_import_diagnostic.json' if diagnostic else 'results/lean_lift_latest.json')).write_text(json.dumps(result, indent=2))
    print(json.dumps(result), flush=True)
