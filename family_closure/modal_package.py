"""Package retained evidence and replay the portable verifier on Modal."""
import hashlib
import json
from pathlib import Path

import modal

HERE = Path(__file__).resolve().parent
app = modal.App('proven-ground-family-evidence-package')
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
)


@app.function(image=image, cpu=1, memory=(2048, 8192), timeout=300,
              nonpreemptible=True, retries=0, volumes={'/results': volume})
def package(files):
    import gzip
    import shutil
    import subprocess
    import time
    import zipfile

    started = time.monotonic()
    root = Path('/results')
    release = root / 'family_supplement_v2'
    release.mkdir(exist_ok=False)

    def put(name, data):
        target = release / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)

    def record(key):
        return json.loads((root / key / 'result.json').read_text())

    def cert(label, cnf, proof, identities):
        target = 'proofs/' + label
        for extension, source in (('cnf', cnf), ('lrat', proof)):
            raw = source.read_bytes()
            if hashlib.sha256(raw).hexdigest() != identities[extension + '_sha256']:
                raise ValueError('source evidence hash mismatch: ' + label)
            previous = root / 'family_supplement_v1' / (target + '.' + extension + '.gz')
            compressed = previous.read_bytes() if previous.exists() else gzip.compress(raw, compresslevel=6, mtime=0)
            if hashlib.sha256(gzip.decompress(compressed)).hexdigest() != identities[extension + '_sha256']:
                raise ValueError('reused compressed evidence mismatch: ' + label)
            put(target + '.' + extension + '.gz', compressed)
        data['certificates'].append(dict(label=label, cnf=target + '.cnf.gz', lrat=target + '.lrat.gz',
                                         cnf_sha256=identities['cnf_sha256'], lrat_sha256=identities['lrat_sha256']))

    for name, content in files.items():
        put(name, content)
    data = dict(networks=[], certificates=[], semantic_scope=
                'K3=36 and K4=67 use the written prefix-isolation/NPN completeness arguments; K5 lower130 is Lean-checked. See PROTOCOL.md and GenericLift.lean.')
    for K in (3, 4, 5):
        summary = record(f'K{K}_exact_pair')
        put(f'records/K{K}_EXACT.json', json.dumps(summary, indent=2).encode())
        filename = 'network130.blif' if K == 5 else 'network.blif'
        target = f'netlists/K{K}_minimum.blif'
        put(target, (root / f'K{K}_exact_pair' / filename).read_bytes())
        data['networks'].append(dict(path=target, K=K, n=K+2, luts=summary['exact_minimum'], depth=summary['levels']))
        if K == 5:
            source = root / 'K5_exact_pair'
            identities = {extension + '_sha256': summary['lower_' + extension + '_sha256'] for extension in ('cnf', 'lrat')}
            cert('K5_any_depth_129', source / 'lower129.cnf', source / 'lower129.lrat', identities)
        else:
            lower = record(summary['lower_key'])
            source = root / summary['lower_key']
            cert(f'K{K}_any_depth_{summary["exact_minimum"]-1}', source / 'instance.cnf', source / 'proof.lrat', lower)
    for K, key in (
        (3, '301c2ca9ab15eaf2_K3_n5_e5_isolation_t180_a97330335a74'),
        (5, '301c2ca9ab15eaf2_K5_n7_e3_isolation_t180_a97330335a74')):
        upper = record(key)
        name = f'netlists/K{K}_depth2.blif'
        put(name, upper['network'].encode())
        data['networks'].append(dict(path=name, K=K, n=K+2, luts=upper['nodes'], depth=upper['levels']))
    for K, key, field, prefix in (
        (3, '301c2ca9ab15eaf2_K3_n5_e4_cert-isolation_t60_a97330335a74', 'trials', 'isolation_'),
        (5, '301c2ca9ab15eaf2_K5_n7_e2_cert-isolation2_t60_a97330335a74', 'cases', 'case')):
        lower = record(key)
        if lower['answer'] != 'CERTIFIED_DEPTH2_LOWER':
            raise ValueError('depth-two case aggregation is incomplete')
        put(f'records/K{K}_depth2_bound.json', json.dumps(lower, indent=2).encode())
        source = root / key
        for i, item in enumerate(lower[field]):
            cert(f'K{K}_depth2_case{i}', source / (prefix + str(i) + '.cnf'),
                 source / (prefix + str(i) + '.lrat'), item)
    put('DATA.json', json.dumps(data, indent=2).encode())
    manifest = {str(path.relative_to(release)).replace('\\', '/'): hashlib.sha256(path.read_bytes()).hexdigest()
                for path in sorted(release.rglob('*')) if path.is_file()}
    put('MANIFEST.json', json.dumps(manifest, indent=2).encode())
    command = ['python', str(release / 'verify_release.py'), '--cake-lpr', '/opt/cake_lpr/cake_lpr']
    proc = subprocess.run(command, capture_output=True, text=True, timeout=180)
    log = root / 'family_supplement_replay.json'
    log.write_text(json.dumps(dict(exit=proc.returncode, stdout=proc.stdout, stderr=proc.stderr,
                                   command=command), indent=2))
    if proc.returncode != 0:
        volume.commit()
        raise ValueError('portable replay failed: ' + proc.stdout + proc.stderr)
    replay = json.loads(proc.stdout)
    archive = root / 'decoder-family-supplement.zip'
    if archive.exists():
        shutil.copyfile(archive, root / 'decoder-family-supplement-v1.zip')
    with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=6) as output:
        for path in sorted(release.rglob('*')):
            if path.is_file():
                output.write(path, str(path.relative_to(release)),
                             compress_type=zipfile.ZIP_STORED if path.suffix == '.gz' else zipfile.ZIP_DEFLATED)
    result = dict(files=len(manifest)+1, networks=len(replay['networks']),
                  accepted_certificates=len(replay['accepted_certificates']),
                  negative_controls=replay['negative_controls'],
                  archive_sha256=hashlib.sha256(archive.read_bytes()).hexdigest(),
                  archive_bytes=archive.stat().st_size,
                  wall_seconds=round(time.monotonic()-started, 3))
    (root / 'family_supplement_manifest.json').write_text(json.dumps(result, indent=2))
    volume.commit()
    return result


@app.local_entrypoint()
def main():
    names = ['README.md', 'PROTOCOL.md', 'verify_release.py', 'GenericLift.lean']
    names += [path.name for path in HERE.glob('*.py') if path.name != 'verify_release.py']
    files = {name: (HERE / name).read_bytes() for name in names}
    files['records/lean_lift.json'] = (HERE / 'results/lean_lift_latest.json').read_bytes()
    result = package.remote(files)
    (HERE / 'results/PACKAGE.json').write_text(json.dumps(result, indent=2))
    print(json.dumps(result), flush=True)
