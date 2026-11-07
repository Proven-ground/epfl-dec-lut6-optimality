"""Independently replay the K=5 exact upper/lower pair on Modal."""
import json
from pathlib import Path
import sys

import modal

HERE = Path(__file__).resolve().parent
LEGACY = HERE.parent / 'evidence' / 'dec' / 'family'
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
for name in ('K5_n7.json', 'reduced_K5_n7.cnf.gz', 'reduced_K5_n7.lrat.gz'):
    image = image.add_local_file(LEGACY / name, '/root/legacy/' + name)
app = modal.App('proven-ground-family-pair-verification')
volume = modal.Volume.from_name('proven-ground-decoder-family-closure')


@app.function(image=image, cpu=1, memory=(2048, 8192), timeout=300,
              nonpreemptible=True, retries=0, volumes={'/results': volume})
def verify(witness):
    import gzip
    import hashlib
    import re
    import subprocess
    import time

    sys.path.insert(0, '/root')
    import isolation_multi

    def sha(data):
        return hashlib.sha256(data).hexdigest()

    start = time.monotonic()
    text = witness['network']
    if sha(text.encode()) != witness['network_sha256']:
        raise ValueError('candidate hash mismatch')
    translated = re.sub(r'\bx(\d+)\b', r'i\1', text)
    translated = re.sub(r'\bo(\d+)\b', r'm\1', translated)
    translated = translated.replace('.names zero\n', '')
    mismatches, count, depth = isolation_multi.simulate(translated, 7)
    if (mismatches, count, depth) != (0, 130, 3):
        raise ValueError(f'independent replay failed: {(mismatches, count, depth)}')
    lines = translated.splitlines()
    row = next(i + 1 for i, line in enumerate(lines) if line.startswith('.names ') and line.endswith(' m0'))
    lines[row] = ('1' if lines[row][0] == '0' else '0') + lines[row][1:]
    corrupted, _, _ = isolation_multi.simulate('\n'.join(lines) + '\n', 7)
    if corrupted <= 0:
        raise ValueError('independent replay accepted corrupted output')
    legacy = json.loads(Path('/root/legacy/K5_n7.json').read_text())
    if (legacy['K'], legacy['n'], legacy['luts_lower']) != (5, 7, 130):
        raise ValueError('wrong predecessor bound')
    folder = Path('/results/K5_exact_pair')
    folder.mkdir(exist_ok=True)
    identities = {}
    for extension in ('cnf', 'lrat'):
        data = gzip.decompress(Path(f'/root/legacy/reduced_K5_n7.{extension}.gz').read_bytes())
        identities[extension] = sha(data)
        if identities[extension] != legacy['lower'][extension + '_sha256']:
            raise ValueError(f'legacy {extension} identity mismatch')
        (folder / ('lower129.' + extension)).write_bytes(data)
    command = ['/opt/cake_lpr/cake_lpr', str(folder / 'lower129.cnf'), str(folder / 'lower129.lrat')]
    check = subprocess.run(command, capture_output=True, text=True, timeout=120)
    if check.returncode != 0 or check.stdout.strip() != 's VERIFIED UNSAT':
        raise ValueError(f'lower-bound replay refused: {check.stdout} {check.stderr}')
    (folder / 'network130.blif').write_text(text)
    (folder / 'cake_lpr.log').write_text(check.stdout + check.stderr)
    result = dict(K=5, n=7, exact_minimum=130, levels=3,
                  independent_simulation_mismatches=mismatches,
                  corrupted_output_mismatches=corrupted, counted_luts=count,
                  network_sha256=witness['network_sha256'], lower_cnf_sha256=identities['cnf'],
                  lower_lrat_sha256=identities['lrat'], cake_lpr_verdict=check.stdout.strip(),
                  cake_command=command, cake_binary_sha256=sha(Path('/opt/cake_lpr/cake_lpr').read_bytes()),
                  independent_checker_sha256=sha(Path('/root/isolation_multi.py').read_bytes()),
                  wall_seconds=round(time.monotonic() - start, 3),
                  bridge='Existing one-helper parametric reduction, as recorded at revision 0ebcd03')
    (folder / 'result.json').write_text(json.dumps(result, indent=2))
    volume.commit()
    return result


@app.local_entrypoint()
def main():
    source = HERE / 'results/301c2ca9ab15eaf2_K5_n7_e2_cascade_t30_da67ba4ab98f.json'
    witness = json.loads(source.read_text())
    result = verify.remote(witness)
    (HERE / 'results/K5_EXACT.json').write_text(json.dumps(result, indent=2))
    (HERE / 'results/K5_n7_130.blif').write_text(witness['network'])
    print(json.dumps(result), flush=True)
