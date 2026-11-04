"""Solve direct cross-check instances on Modal, one container per (instance, seed), with no duplicated work.

One app, one image, one volume:
  - the image builds CaDiCaL from the pinned commit once; Modal caches the built image and reuses it for every run;
  - the instance is generated inside the container from direct_roles.py, so nothing large is uploaded;
  - every result is stored on the volume under a key made of the encoder's SHA-256, K, n, EXTRA, the seed and the
    CaDiCaL commit; a run whose key already holds a result returns it without solving, so a repeated launch costs a
    lookup, never a second solve.
A satisfying assignment is decoded, simulated on every pattern and checked before it is stored.

    python -m modal run --detach crosscheck/modal_solve.py --k 6 --n 7 --extra 1 --seeds 1
One seed per invocation, so each finishes with its own notice and the other can be stopped the moment one answers.
"""
import hashlib
import json
from pathlib import Path, PurePosixPath

import modal

CADICAL_COMMIT = 'c60730422e758ef1cebe7aeddf2dda31c996bf04'  # rel-3.0.1, the solver the paper's evidence used
REMOTE_ENCODER = PurePosixPath('/root/crosscheck/direct_roles.py')  # container path, POSIX on every host
LOCAL_ENCODER = Path(__file__).resolve().parent / 'direct_roles.py'
ENCODER = LOCAL_ENCODER if LOCAL_ENCODER.exists() else Path(str(REMOTE_ENCODER))  # module also loads in the container
ENCODER_SHA = hashlib.sha256(ENCODER.read_bytes()).hexdigest()

app = modal.App('proving-ground-crosscheck')
image = (
    modal.Image.debian_slim(python_version='3.11')
    .apt_install('git', 'build-essential')
    .run_commands(
        'git clone https://github.com/arminbiere/cadical /opt/cadical',
        f'cd /opt/cadical && git checkout {CADICAL_COMMIT} && ./configure && make -j4',
    )
    .add_local_file(LOCAL_ENCODER, str(REMOTE_ENCODER))
)
results = modal.Volume.from_name('proving-ground-crosscheck-results', create_if_missing=True)


def key(K, n, extra, seed):
    return f'{ENCODER_SHA[:16]}_K{K}_n{n}_e{extra}_seed{seed}_cadical{CADICAL_COMMIT[:8]}'


# Cost shape. CaDiCaL is single-threaded: one busy thread is half a physical core, so cpu=0.5 (Modal's unit is the
# physical core, billed at the higher of request and usage). The local run of this instance peaked at 4.4 GB, so the
# memory request is 5 GiB with a hard limit of 12 GiB, and the timeout is Modal's 24-hour maximum. At Modal's list
# prices ($0.0000131 per core-second, $0.00000222 per GiB-second) the worst case per container, full 24 hours at the
# 12 GiB limit, is $0.57 CPU + $2.30 memory = $2.87, or $3.43 if a thread were billed as a whole core.
@app.function(image=image, cpu=0.5, memory=(5120, 12288), timeout=86400, volumes={'/results': results})
def solve(K: int, n: int, extra: int, seed: int) -> dict:
    import subprocess
    import sys
    import time
    out = Path('/results') / (key(K, n, extra, seed) + '.json')
    results.reload()
    if out.exists():
        return {**json.loads(out.read_text()), 'cached': True}
    sys.path.insert(0, str(REMOTE_ENCODER.parent))
    import direct_roles
    cnf = '/tmp/instance.cnf'
    started = time.monotonic()
    nv, nc, meta = direct_roles.build(cnf, K, n, extra)
    generated = round(time.monotonic() - started, 1)
    instance_sha = hashlib.sha256(Path(cnf).read_bytes()).hexdigest()
    started = time.monotonic()
    run = subprocess.run(['/opt/cadical/build/cadical', '-q', f'--seed={seed}', cnf], capture_output=True, text=True)
    record = {'K': K, 'n': n, 'extra': extra, 'seed': seed, 'variables': nv, 'clauses': nc,
              'instance_sha256': instance_sha, 'encoder_sha256': ENCODER_SHA, 'cadical_commit': CADICAL_COMMIT,
              'generate_seconds': generated, 'solve_seconds': round(time.monotonic() - started, 1),
              'exit': run.returncode}
    if run.returncode == 20:
        record['answer'] = 'UNSATISFIABLE'
    elif run.returncode == 10:
        nodes, order = direct_roles.decode(direct_roles.read_model(run.stdout), meta)
        record['answer'] = 'SATISFIABLE'
        record['simulation_mismatches'] = direct_roles.simulate(nodes, order, K, n)
        record['network'] = [{'node': j, 'fanin': nodes[j][0], 'table': hex(nodes[j][1])} for j in order]
    else:
        record['answer'] = 'ERROR'
        record['tail'] = (run.stdout + run.stderr)[-500:]
    out.write_text(json.dumps(record, indent=1))
    results.commit()
    return {**record, 'cached': False}


@app.local_entrypoint()
def main(k: int = 6, n: int = 7, extra: int = 1, seeds: str = '1,2'):
    jobs = [(k, n, extra, int(s)) for s in seeds.split(',')]
    for job, result in zip(jobs, solve.starmap(jobs, return_exceptions=True)):
        if isinstance(result, Exception):
            print(json.dumps({'job': job, 'error': repr(result)}))
            continue
        brief = {x: result.get(x) for x in ('K', 'n', 'extra', 'seed', 'answer', 'solve_seconds', 'clauses',
                                            'simulation_mismatches', 'cached', 'instance_sha256')}
        print(json.dumps(brief))
