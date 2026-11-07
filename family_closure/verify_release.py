"""Replay the decoder family supplement using Python and cake_lpr."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check_inventory(data):
    expected_networks = {
        ('netlists/K3_minimum.blif', 3, 5, 36, 3),
        ('netlists/K3_depth2.blif', 3, 5, 37, 2),
        ('netlists/K4_minimum.blif', 4, 6, 67, 2),
        ('netlists/K5_minimum.blif', 5, 7, 130, 3),
        ('netlists/K5_depth2.blif', 5, 7, 131, 2),
    }
    actual = [(item['path'], item['K'], item['n'], item['luts'], item['depth'])
              for item in data['networks']]
    if len(actual) != len(expected_networks) or set(actual) != expected_networks:
        raise ValueError('required network inventory is missing, duplicated or changed')
    expected_certificates = {'K3_any_depth_35', 'K4_any_depth_66', 'K5_any_depth_129'}
    expected_certificates.update(f'K3_depth2_case{i}' for i in range(17))
    expected_certificates.update(f'K5_depth2_case{i}' for i in range(3))
    labels = [item['label'] for item in data['certificates']]
    if len(labels) != len(expected_certificates) or set(labels) != expected_certificates:
        raise ValueError('required certificate inventory is missing or duplicated')


def circuit(text, n, K, expected):
    nodes, inputs, outputs, current = [], [], [], None
    for row in text.splitlines():
        parts = row.split()
        if not parts or parts[0].startswith('#'):
            continue
        if parts[0] == '.inputs':
            inputs = parts[1:]
        elif parts[0] == '.outputs':
            outputs = parts[1:]
        elif parts[0] == '.names':
            current = (parts[1:-1], parts[-1], [])
            nodes.append(current)
            if len(current[0]) > K:
                raise ValueError('LUT pin limit exceeded')
        elif not parts[0].startswith('.'):
            if current is None or len(parts) != 2 or parts[1] != '1':
                raise ValueError('invalid BLIF cube')
            if len(parts[0]) != len(current[0]) or any(c not in '01-' for c in parts[0]):
                raise ValueError('invalid BLIF pattern')
            current[2].append(parts[0])
    count = sum(bool(pins) for pins, _, _ in nodes)
    if len(inputs) != n or len(outputs) != 1 << n or len(set(outputs)) != len(outputs) or count != expected:
        raise ValueError('wrong input, output or counted LUT inventory')
    depth = {name: 0 for name in inputs}
    for pins, output, _ in nodes:
        if output in depth or any(pin not in depth for pin in pins):
            raise ValueError('duplicate node or cyclic/undefined fanin')
        depth[output] = 1 + max((depth[pin] for pin in pins), default=-1)
    for x in range(1 << n):
        values = {name: (x >> i) & 1 for i, name in enumerate(inputs)}
        for pins, output, cubes in nodes:
            values[output] = int(any(all(c == '-' or int(c) == values[pin]
                                         for c, pin in zip(cube, pins)) for cube in cubes))
        for q, output in enumerate(outputs):
            if values[output] != int(x == q):
                raise ValueError(f'wrong minterm: input {x}, output {q}')
    return dict(inputs=n, patterns=1 << n, luts=count, depth=max(depth[o] for o in outputs))


def verify(root, cake):
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    for name, expected in manifest.items():
        if digest((root / name).read_bytes()) != expected:
            raise ValueError(f'artifact identity mismatch: {name}')
    data = json.loads((root / 'DATA.json').read_text())
    check_inventory(data)
    for altered, expected_message in (
        ({**data, 'networks': data['networks'][1:]}, 'required network inventory'),
        ({**data, 'certificates': data['certificates'][1:]}, 'required certificate inventory'),
        ({**data, 'certificates': data['certificates'][:-1] + [data['certificates'][0]]}, 'required certificate inventory'),
    ):
        try:
            check_inventory(altered)
        except ValueError as error:
            if expected_message not in str(error):
                raise
        else:
            raise ValueError('incomplete or duplicated evidence escaped inventory check')
    results = []
    for item in data['networks']:
        result = circuit((root / item['path']).read_text(), item['n'], item['K'], item['luts'])
        if result['depth'] != item['depth']:
            raise ValueError('unexpected logic depth')
        results.append(dict(path=item['path'], **result))
    checks = []
    with tempfile.TemporaryDirectory() as temp:
        folder = Path(temp)
        for item in data['certificates']:
            for extension in ('cnf', 'lrat'):
                raw = gzip.decompress((root / item[extension]).read_bytes())
                if digest(raw) != item[extension + '_sha256']:
                    raise ValueError(f'decompressed {extension} identity mismatch')
                (folder / extension).write_bytes(raw)
            proc = subprocess.run([cake, str(folder / 'cnf'), str(folder / 'lrat')],
                                  capture_output=True, text=True, timeout=120)
            if proc.returncode != 0 or proc.stdout.strip() != 's VERIFIED UNSAT':
                raise ValueError(f'certificate refused: {item["label"]}: {proc.stdout} {proc.stderr}')
            checks.append(item['label'])
        bad = folder / 'invalid.lrat'
        bad.write_text('1 0 0\n')
        proc = subprocess.run([cake, str(folder / 'cnf'), str(bad)], capture_output=True, text=True, timeout=20)
        if 's VERIFIED UNSAT' in proc.stdout.splitlines():
            raise ValueError('invalid LRAT accepted')
    first = data['networks'][0]
    text = (root / first['path']).read_text()
    lines = text.splitlines()
    row = next(i + 1 for i, line in enumerate(lines) if line.startswith('.names ') and line.endswith(' o0'))
    lines[row] = ('1' if lines[row][0] == '0' else '0') + lines[row][1:]
    try:
        circuit('\n'.join(lines), first['n'], first['K'], first['luts'])
    except ValueError as error:
        if 'wrong minterm' not in str(error):
            raise
    else:
        raise ValueError('corrupted circuit accepted')
    return dict(networks=results, accepted_certificates=checks,
                negative_controls=['missing circuit rejected', 'missing certificate rejected',
                                   'duplicate certificate rejected', 'wrong minterm rejected',
                                   'malformed LRAT rejected'],
                semantic_scope=data['semantic_scope'])


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--directory', type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument('--cake-lpr', required=True)
    options = parser.parse_args()
    print(json.dumps(verify(options.directory, options.cake_lpr), indent=2))
