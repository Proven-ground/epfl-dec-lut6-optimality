"""The decoder family on Modal: for (K, n) = (3, 5), (4, 6), (5, 7), the certified lower bound 2^n + 2 and the
two-shared-LUT construction; and cake_lpr on the Lean formula lean/bound.cnf with its refutation lean/bound.lrat.
Nothing runs on the launching machine.

    python -m modal run family/modal_family.py

One image builds CaDiCaL (rel-3.0.1) and cake_lpr (commit a36874a8) from source. The lower-bound instance is the
paper's reduction, written by crosscheck/reduced_bound.py for (K, n), refuted by CaDiCaL with an LRAT proof that
cake_lpr checks. The construction is the isolation instance of family.py, solved by CaDiCaL; a model is decoded,
written as a netlist and simulated on every pattern before it is reported. Results are written next to this file.
"""
import gzip
import hashlib
import json
import subprocess
import sys
import time
from pathlib import Path

import modal

HERE = Path(__file__).resolve().parent
CADICAL_COMMIT = 'c60730422e758ef1cebe7aeddf2dda31c996bf04'
CAKE_LPR_COMMIT = 'a36874a8b750b43fe4b385b8ddbf5b033e46a3fa'

app = modal.App('proving-ground-family')
image = (
    modal.Image.debian_slim(python_version='3.11')
    .apt_install('git', 'build-essential')
    .run_commands(
        'git clone https://github.com/arminbiere/cadical /opt/cadical',
        f'cd /opt/cadical && git checkout {CADICAL_COMMIT} && ./configure && make -j4',
        'git clone https://github.com/tanyongkiam/cake_lpr /opt/cake_lpr',
        f'cd /opt/cake_lpr && git checkout {CAKE_LPR_COMMIT} && make',
    )
    .add_local_file(HERE / 'family.py', '/root/family/family.py')
    .add_local_file(HERE.parent / 'crosscheck' / 'reduced_bound.py', '/root/family/reduced_bound.py')
)
CADICAL = '/opt/cadical/build/cadical'
CAKE_LPR = '/opt/cake_lpr/cake_lpr'
lean_volume = modal.Volume.from_name('proving-ground-lean')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def run(cmd, timeout):
    started = time.monotonic()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
    return proc, round(time.monotonic() - started, 1)


def tools():
    return {'cadical_commit': CADICAL_COMMIT, 'cadical_sha256': sha(CADICAL),
            'cake_lpr_commit': CAKE_LPR_COMMIT, 'cake_lpr_sha256': sha(CAKE_LPR)}


@app.function(image=image, cpu=2, memory=8192, timeout=7200)
def family(K: int, n: int, lower_bound: bool = True) -> dict:
    sys.path.insert(0, '/root/family')
    import family as fam
    import reduced_bound
    work = Path('/tmp/work')
    work.mkdir(exist_ok=True)
    record = {'K': K, 'n': n, 'luts_lower': (1 << n) + 2, **tools()}
    # lower bound: 2^n + 1 LUT-K nodes are impossible (the reduction, refuted and certified)
    if lower_bound:
        cnf, lrat = work / f'reduced_K{K}_n{n}.cnf', work / f'reduced_K{K}_n{n}.lrat'
        nv, nc = reduced_bound.write(str(cnf), K, n)
        proc, seconds = run([CADICAL, '-q', '--lrat', '--binary=false', str(cnf), str(lrat)], 3600)
        lower = {'variables': nv, 'clauses': nc, 'cnf_sha256': sha(cnf), 'cadical_exit': proc.returncode,
                 'cadical_seconds': seconds}
        if proc.returncode == 20:
            check, cseconds = run([CAKE_LPR, str(cnf), str(lrat)], 3600)
            lower.update({'lrat_bytes': lrat.stat().st_size, 'lrat_sha256': sha(lrat),
                          'cake_lpr_stdout': check.stdout.strip(), 'cake_lpr_stderr': check.stderr.strip()[-500:],
                          'cake_lpr_seconds': cseconds, 'verified': check.stdout.strip() == 's VERIFIED UNSAT'})
            record['reduced_cnf_gz'] = gzip.compress(cnf.read_bytes(), 9, mtime=0)
            record['reduced_lrat_gz'] = gzip.compress(lrat.read_bytes(), 9, mtime=0)
        record['lower'] = lower
    # upper bound: two shared LUTs
    upper = []
    for supports in fam.classes(K, n):
        count, clauses = fam.isolation_cnf(K, n, supports)
        iso = work / f'isolation_K{K}_n{n}_{supports[1][0]}.cnf'
        iso.write_text(fam.dimacs(count, clauses))
        proc, seconds = run([CADICAL, '-q', str(iso)], 3600)
        entry = {'supports': supports, 'variables': count, 'clauses': len(clauses), 'cnf_sha256': sha(iso),
                 'cadical_exit': proc.returncode, 'cadical_seconds': seconds}
        if proc.returncode == 10:
            tables = fam.decode(fam.read_model(proc.stdout), K)
            blif = fam.network(K, n, supports, tables)
            mism, luts, levels = fam.simulate(blif, n)
            entry.update({'satisfiable': True, 'tables': [hex(t) for t in tables], 'blif': blif,
                          'simulation_mismatches': mism, 'luts': luts, 'levels': levels,
                          'valid': mism == 0 and luts == (1 << n) + 2 and levels == 2})
        elif proc.returncode == 20:
            entry['satisfiable'] = False
        else:
            entry['error'] = (proc.stdout + proc.stderr)[-500:]
        upper.append(entry)
    record['upper'] = upper
    return record


@app.function(image=image, cpu=2, memory=24576, timeout=14400, volumes={'/lean': lean_volume})
def lean_certificate() -> dict:
    cnf, lrat = '/lean/project/bound.cnf', '/lean/project/bound.lrat'
    record = {'cnf': 'lean/bound.cnf', 'cnf_bytes': Path(cnf).stat().st_size, 'cnf_sha256': sha(cnf),
              'lrat': 'lean/bound.lrat', 'lrat_bytes': Path(lrat).stat().st_size, 'lrat_sha256': sha(lrat),
              **tools()}
    proc, seconds = run([CAKE_LPR, '--CML_HEAP_SIZE=16000', '--CML_STACK_SIZE=4000', cnf, lrat], 14000)
    record.update({'command': 'cake_lpr --CML_HEAP_SIZE=16000 --CML_STACK_SIZE=4000 bound.cnf bound.lrat',
                   'exit': proc.returncode, 'stdout': proc.stdout.strip(), 'stderr': proc.stderr.strip()[-1000:],
                   'seconds': seconds, 'verified': proc.stdout.strip() == 's VERIFIED UNSAT'})
    return record


@app.local_entrypoint()
def main(cases: str = '3-5,4-6,5-7', lower_bound: bool = True, lean: bool = True):
    """`--cases 6-7,6-8 --no-lower-bound --no-lean` runs the construction alone as a positive control: the paper's
    one- and two-shared-LUT networks exist there, so the isolation instance must be satisfiable."""
    cert = lean_certificate.spawn() if lean else None
    jobs = [tuple(int(v) for v in c.split('-')) + (lower_bound,) for c in cases.split(',')]
    failed = 0
    for (K, n, _), rec in zip(jobs, family.starmap(jobs, return_exceptions=True, wrap_returned_exceptions=False)):
        if isinstance(rec, Exception):
            print(json.dumps({'K': K, 'n': n, 'error': repr(rec)}))
            failed += 1
            continue
        for key in ('reduced_cnf_gz', 'reduced_lrat_gz'):
            if key in rec:
                (HERE / f"reduced_K{K}_n{n}.{key.split('_')[1]}.gz").write_bytes(rec.pop(key))
        found = next((u for u in rec['upper'] if u.get('valid')), None)
        if found:
            (HERE / f'K{K}_n{n}.blif').write_text(found['blif'], newline='\n')
        for u in rec['upper']:
            u.pop('blif', None)
        (HERE / f'K{K}_n{n}.json').write_text(json.dumps(rec, indent=1), newline='\n')
        lower_ok = rec['lower'].get('verified') if 'lower' in rec else None
        print(json.dumps({'K': K, 'n': n, 'lower_verified': lower_ok,
                          'lower_seconds': rec['lower'].get('cadical_seconds') if 'lower' in rec else None,
                          'upper': [{k: u.get(k) for k in ('supports', 'satisfiable', 'valid', 'cadical_seconds')}
                                    for u in rec['upper']]}))
        failed += lower_ok is False
    if cert is not None:
        rec = cert.get()
        (HERE.parent.parent.parent / 'lean' / 'bound.cake_lpr.json').write_text(json.dumps(rec, indent=1),
                                                                                newline='\n')
        print(json.dumps({k: rec.get(k) for k in ('cnf_sha256', 'lrat_sha256', 'stdout', 'seconds', 'verified',
                                                  'exit', 'stderr')}))
        failed += not rec.get('verified')
    if failed:
        raise SystemExit(f'{failed} result(s) not verified')
