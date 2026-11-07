"""Independent exhaustive circuit replay and certificate replay for K3 and K4."""
import hashlib
import json
from pathlib import Path

import modal

HERE = Path(__file__).resolve().parent
app = modal.App('proven-ground-family-final-replay')
volume = modal.Volume.from_name('proven-ground-decoder-family-closure')
image = (
    modal.Image.debian_slim(python_version='3.11')
    .apt_install('git', 'build-essential')
    .run_commands(
        'git clone https://github.com/arminbiere/cadical /opt/cadical',
        'cd /opt/cadical && git checkout c60730422e758ef1cebe7aeddf2dda31c996bf04 && ./configure && make -j4',
        'git clone https://github.com/tanyongkiam/cake_lpr /opt/cake_lpr',
        'cd /opt/cake_lpr && git checkout a36874a8b750b43fe4b385b8ddbf5b033e46a3fa && make',
    )
    .add_local_file(HERE / 'isolation_multi.py', '/root/isolation_multi.py')
)


@app.function(image=image, cpu=1, memory=(2048, 8192), timeout=300,
              nonpreemptible=True, retries=0, volumes={'/results': volume})
def verify(K, witness, lower):
    import re
    import subprocess
    import sys
    import time

    sys.path.insert(0, '/root')
    import isolation_multi

    def sha(data):
        return hashlib.sha256(data).hexdigest()

    started = time.monotonic()
    n, minimum = K + 2, witness['nodes']
    if lower['answer'] != 'CERTIFIED_UNSAT' or (lower['K'], lower['n']) != (K, n):
        raise ValueError('lower-bound record is not a certified case for these parameters')
    if minimum != (1 << n) + lower['extra'] + 1:
        raise ValueError('upper and lower counts do not meet')
    text = witness['network']
    if sha(text.encode()) != witness['network_sha256']:
        raise ValueError('candidate hash mismatch')
    translated = re.sub(r'\bx(\d+)\b', r'i\1', text)
    translated = re.sub(r'\bo(\d+)\b', r'm\1', translated)
    translated = translated.replace('.names zero\n', '')
    mismatches, count, depth = isolation_multi.simulate(translated, n)
    if (mismatches, count, depth) != (0, minimum, witness['levels']):
        raise ValueError(f'independent replay failed: {(mismatches, count, depth)}')
    maximum_fanin = max(len(row.split()) - 2 for row in translated.splitlines() if row.startswith('.names '))
    if maximum_fanin > K:
        raise ValueError('a counted LUT exceeds the pin budget')
    lines = translated.splitlines()
    row = next(i + 1 for i, line in enumerate(lines) if line.startswith('.names ') and line.endswith(' m0'))
    lines[row] = ('1' if lines[row][0] == '0' else '0') + lines[row][1:]
    corrupted, _, _ = isolation_multi.simulate('\n'.join(lines) + '\n', n)
    if corrupted <= 0:
        raise ValueError('corrupted candidate escaped independent replay')
    source = Path('/results') / lower['key']
    identities = {}
    for extension in ('cnf', 'lrat'):
        identities[extension] = sha((source / ('instance.cnf' if extension == 'cnf' else 'proof.lrat')).read_bytes())
        if identities[extension] != lower[extension + '_sha256']:
            raise ValueError(f'{extension} identity mismatch')
    folder = Path(f'/results/K{K}_exact_pair')
    folder.mkdir(exist_ok=True)
    command = ['/opt/cake_lpr/cake_lpr', str(source / 'instance.cnf'), str(source / 'proof.lrat')]
    completed = subprocess.run(command, capture_output=True, text=True, timeout=120)
    if completed.returncode != 0 or completed.stdout.strip() != 's VERIFIED UNSAT':
        raise ValueError(f'certificate replay refused: {completed.stdout} {completed.stderr}')
    bad = folder / 'invalid.lrat'
    bad.write_text('1 0 0\n')
    negative = subprocess.run(command[:2] + [str(bad)], capture_output=True, text=True, timeout=20)
    if 's VERIFIED UNSAT' in negative.stdout.splitlines():
        raise ValueError('invalid certificate accepted')
    (folder / 'network.blif').write_text(text)
    (folder / 'lower_record.json').write_text(json.dumps(lower, indent=2))
    (folder / 'upper_record.json').write_text(json.dumps(witness, indent=2))
    (folder / 'cake_lpr.log').write_text(completed.stdout + completed.stderr)
    (folder / 'invalid_certificate.log').write_text(negative.stdout + negative.stderr)
    record = dict(K=K, n=n, exact_minimum=minimum, levels=depth,
                  counted_luts=count, maximum_fanin=maximum_fanin,
                  independent_simulation_mismatches=mismatches, corrupted_output_mismatches=corrupted,
                  network_sha256=witness['network_sha256'], lower_key=lower['key'],
                  lower_cnf_sha256=identities['cnf'], lower_lrat_sha256=identities['lrat'],
                  cake_lpr_verdict=completed.stdout.strip(), cake_command=command,
                  invalid_certificate_exit=negative.returncode,
                  invalid_certificate_output=negative.stdout + negative.stderr,
                  cake_binary_sha256=sha(Path('/opt/cake_lpr/cake_lpr').read_bytes()),
                  independent_checker_sha256=sha(Path('/root/isolation_multi.py').read_bytes()),
                  wall_seconds=round(time.monotonic() - started, 3),
                  proof_scope='Exact minimum conditional on the documented prefix-isolation and NPN completeness arguments; those new bridges are not yet Lean-checked')
    (folder / 'result.json').write_text(json.dumps(record, indent=2))
    volume.commit()
    return record


@app.local_entrypoint()
def main():
    cases = [
        (3, '6370f9dfc4715a68_K3_n5_e4_sym-search_t120_f85718df5105',
         '6370f9dfc4715a68_K3_n5_e3_sym-search_t120_f85718df5105'),
        (4, '301c2ca9ab15eaf2_K4_n6_e3_isolation_t180_a97330335a74',
         '6370f9dfc4715a68_K4_n6_e2_sym-search_t120_f85718df5105'),
    ]
    for K, upper, lower in cases:
        witness = json.loads((HERE / 'results' / (upper + '.json')).read_text())
        bound = json.loads((HERE / 'results' / (lower + '.json')).read_text())
        result = verify.remote(K, witness, bound)
        (HERE / f'results/K{K}_EXACT.json').write_text(json.dumps(result, indent=2))
        (HERE / f'results/K{K}_n{K+2}_{witness["nodes"]}.blif').write_text(witness['network'])
        print(json.dumps(result), flush=True)
