"""Decoder-family experiments. All scientific computation executes inside Modal."""
import hashlib
import json
from pathlib import Path

import modal

HERE = Path(__file__).resolve().parent
RUNNER_SHA256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
CADICAL_COMMIT = 'c60730422e758ef1cebe7aeddf2dda31c996bf04'
CAKE_COMMIT = 'a36874a8b750b43fe4b385b8ddbf5b033e46a3fa'
app = modal.App('proven-ground-decoder-family-closure')
image = (
    modal.Image.debian_slim(python_version='3.11')
    .apt_install('git', 'build-essential')
    .run_commands(
        'git clone https://github.com/arminbiere/cadical /opt/cadical',
        f'cd /opt/cadical && git checkout {CADICAL_COMMIT} && ./configure && make -j4',
        'git clone https://github.com/tanyongkiam/cake_lpr /opt/cake_lpr',
        f'cd /opt/cake_lpr && git checkout {CAKE_COMMIT} && make',
    )
    .add_local_file(HERE / 'direct_multi.py', '/root/direct_multi.py')
    .add_local_file(HERE / 'direct_compact.py', '/root/direct_compact.py')
    .add_local_file(HERE / 'direct_reduced.py', '/root/direct_reduced.py')
    .add_local_file(HERE / 'isolation_multi.py', '/root/isolation_multi.py')
    .add_local_file(HERE / 'cascade.py', '/root/cascade.py')
    .add_local_file(HERE / 'feedback.py', '/root/feedback.py')
    .add_local_file(HERE / 'helper_bound.py', '/root/helper_bound.py')
    .add_local_file(HERE / 'isolation_bound.py', '/root/isolation_bound.py')
    .add_local_file(HERE / 'isolation_symmetric.py', '/root/isolation_symmetric.py')
)
volume = modal.Volume.from_name('proven-ground-decoder-family-closure', create_if_missing=True)


@app.function(image=image, cpu=1, memory=(2048, 8192), timeout=1200,
              nonpreemptible=True, retries=0, max_containers=1, volumes={'/results': volume})
def experiment(K: int, n: int, extra: int, seconds: int = 300, mode: str = 'search'):
    import gzip
    import itertools
    import resource
    import shutil
    import subprocess
    import sys
    import time

    sys.path.insert(0, '/root')
    compact = mode.startswith('compact-')
    reduced = mode.startswith('reduced-')
    symmetric = mode.startswith('sym-')
    isolation_reduction = mode.startswith('iso-') or symmetric
    helper_reduction = mode.startswith('helper-') or isolation_reduction
    original_mode = mode
    if symmetric:
        import isolation_symmetric as direct
        mode = mode[len('sym-'):]
    elif isolation_reduction:
        import isolation_bound as direct
        mode = mode[len('iso-'):]
    elif helper_reduction:
        import helper_bound as direct
        mode = mode[len('helper-'):]
    elif reduced:
        import direct_reduced as direct
        mode = mode[len('reduced-'):]
    elif compact:
        import direct_compact as direct
        mode = mode[len('compact-'):]
    else:
        import direct_multi as direct

    def sha(path):
        h = hashlib.sha256()
        with open(path, 'rb') as source:
            for block in iter(lambda: source.read(1024 * 1024), b''):
                h.update(block)
        return h.hexdigest()

    encoder_hash = sha('/root/isolation_symmetric.py' if symmetric else
                       '/root/isolation_bound.py' if isolation_reduction else
                       '/root/helper_bound.py' if helper_reduction else
                       '/root/direct_reduced.py' if reduced else
                       '/root/direct_compact.py' if compact else '/root/direct_multi.py')
    key = f'{encoder_hash[:16]}_K{K}_n{n}_e{extra}_{original_mode}_t{seconds}'
    if symmetric:
        key += '_' + sha('/root/isolation_bound.py')[:12]
    if mode in ('isolation', 'cert-isolation', 'cert-isolation2'):
        key += '_' + sha('/root/isolation_multi.py')[:12]
    if mode in ('cascade', 'cert-cascade', 'cascade3', 'feedback'):
        key += '_' + sha('/root/' + ('feedback' if mode == 'feedback' else 'cascade') + '.py')[:12]
    folder = Path('/results') / key
    folder.mkdir(exist_ok=True)
    result_file = folder / 'result.json'
    if result_file.exists():
        record = json.loads(result_file.read_text())
        if record.get('answer') in ('SAT', 'CERTIFIED_UNSAT', 'VERIFIED_UPPER'):
            return {**record, 'cached': True}
    start = time.monotonic()
    record = dict(K=K, n=n, extra=extra, mode=mode, key=key,
                  encoder_sha256=encoder_hash, cadical_commit=CADICAL_COMMIT,
                  cake_commit=CAKE_COMMIT, runner_sha256=RUNNER_SHA256)

    def save():
        record['wall_seconds'] = round(time.monotonic() - start, 3)
        record['max_rss_kib'] = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
        result_file.write_text(json.dumps(record, indent=2))
        volume.commit()
        return record

    def emit_and_verify(nodes):
        mismatches = direct.simulate(nodes, None, K, n)
        if mismatches != 0:
            raise ValueError(f'decoded decoder failed simulation: {mismatches}')
        order = direct.topological(nodes, n, K)
        names = [f'x{i}' for i in range(n)] + ['zero']
        names += [f'o{i}' for i in range(1 << n)]
        names += [f'h{i}' for i in range(len(nodes) - (1 << n))]
        lines = ['.model decoder', '.inputs ' + ' '.join(names[:n]),
                 '.outputs ' + ' '.join(f'o{i}' for i in range(1 << n)), '.names zero']
        depth = {}
        for j in order:
            pins, table = nodes[j]
            output = names[n + 1 + j]
            lines.append('.names ' + ' '.join(names[s] for s in pins) + ' ' + output)
            for row in range(1 << K):
                if (table >> row) & 1:
                    lines.append(''.join(str((row >> p) & 1) for p in range(K)) + ' 1')
            depth[j] = 1 + max([depth[s - n - 1] for s in pins if s > n] or [0])
        lines.append('.end')
        text = '\n'.join(lines) + '\n'
        blif = folder / 'network.blif'
        blif.write_text(text)
        # Separate BLIF parser and evaluator. Its oracle is the decoder definition.
        tables = []
        current = None
        for line in text.splitlines():
            words = line.split()
            if words[0] == '.names':
                current = (words[1:-1], words[-1], [])
                tables.append(current)
            elif words[0][0] != '.':
                current[2].append(words[0])
        bad = 0
        for x in range(1 << n):
            values = {f'x{i}': (x >> i) & 1 for i in range(n)}
            for pins, output, rows in tables:
                pattern = ''.join(str(values[p]) for p in pins)
                values[output] = int(pattern in rows)
            bad += sum(values[f'o{i}'] != int(x == i) for i in range(1 << n))
        if bad:
            raise ValueError(f'BLIF replay failed: {bad}')
        record.update(nodes=len(nodes), levels=max(depth[i] for i in range(1 << n)),
                      simulation_mismatches=mismatches, blif_replay_mismatches=bad,
                      network_sha256=sha(blif), network=text)

    if mode == 'cert-isolation2':
        import isolation_multi as isolation
        record['isolation_encoder_sha256'] = sha('/root/isolation_multi.py')
        record['cases'] = []
        for index, supports in enumerate(isolation.classes(K, n)):
            count, clauses = isolation.isolation_cnf(K, n, supports)
            cnf = folder / f'case{index}.cnf'
            proof = folder / f'case{index}.lrat'
            log = folder / f'case{index}.log'
            cnf.write_text(isolation.dimacs(count, clauses))
            with log.open('w') as output:
                try:
                    solved = subprocess.run(['/opt/cadical/build/cadical', '-t', str(seconds),
                                             '--lrat', '--binary=false', str(cnf), str(proof)],
                                            stdout=output, stderr=subprocess.STDOUT, timeout=seconds + 30)
                    code = solved.returncode
                except subprocess.TimeoutExpired:
                    code = None
            case = dict(supports=supports, variables=count, clauses=len(clauses),
                        cnf_sha256=sha(cnf), solver_exit=code, verified=False)
            if code == 20:
                checked = subprocess.run(['/opt/cake_lpr/cake_lpr', str(cnf), str(proof)],
                                         capture_output=True, text=True, timeout=120)
                case.update(cake_output=checked.stdout, cake_exit=checked.returncode,
                            lrat_sha256=sha(proof),
                            verified=checked.returncode == 0 and checked.stdout.strip() == 's VERIFIED UNSAT')
                (folder / f'case{index}.cake.log').write_text(checked.stdout + checked.stderr)
            for path in (cnf, proof):
                if path.exists():
                    with path.open('rb') as source, gzip.open(str(path) + '.gz', 'wb', compresslevel=3) as target:
                        shutil.copyfileobj(source, target)
            record['cases'].append(case)
            if not case['verified']:
                record['answer'] = 'UNRESOLVED'
                return save()
        record.update(answer='CERTIFIED_DEPTH2_LOWER', depth2_lower=(1 << n) + 3,
                      scope='all two-level networks; support pairs modulo primary-input permutation')
        return save()

    if mode in ('cascade', 'cert-cascade', 'cascade3', 'feedback'):
        feedback = mode == 'feedback'
        if feedback:
            import feedback as cascade
        else:
            import cascade
        record['construction_encoder_sha256'] = sha('/root/' + ('feedback' if feedback else 'cascade') + '.py')
        record['trials'] = []
        configurations = []
        if feedback:
            for uses_first in (False, True):
                raw_count = K - 1 - int(uses_first)
                for overlap in range(max(0, raw_count - (n - K)), raw_count + 1):
                    raw = list(range(overlap)) + list(range(K, K + raw_count - overlap))
                    configurations.append([list(range(K)), raw + ([n] if uses_first else []) + [n + 2]])
        elif mode == 'cascade3':
            second_supports = []
            for uses_first in (False, True):
                raw_count = K - int(uses_first)
                for overlap in range(max(0, raw_count - (n - K)), raw_count + 1):
                    raw = list(range(overlap)) + list(range(K, K + raw_count - overlap))
                    second_supports.append(raw + ([n] if uses_first else []))
            for second in second_supports:
                for third in itertools.combinations(range(n + 2), K):
                    if any(signal >= n for signal in third):
                        configurations.append([list(range(K)), second, list(third)])
        else:
            for overlap in range(max(0, K - 1 - (n - K)), K):
                raw = list(range(overlap)) + list(range(K, K + K - 1 - overlap))
                configurations.append([list(range(K)), raw + [n]])
        deadline = start + seconds
        for index, supports in enumerate(configurations):
            if mode == 'cascade3' and deadline - time.monotonic() < 2:
                break
            count, clauses = cascade.isolation_cnf(K, n, supports)
            cnf = folder / f'{mode}_{index}.cnf'
            cnf.write_text(cascade.dimacs(count, clauses))
            log = folder / f'{mode}_{index}.log'
            limit = min(2, max(1, int(deadline - time.monotonic()))) if mode == 'cascade3' else seconds
            proof = folder / f'{mode}_{index}.lrat'
            command = ['/opt/cadical/build/cadical', '-t', str(limit), '--seed=1']
            command += (['--lrat', '--binary=false', str(cnf), str(proof)]
                        if mode == 'cert-cascade' else [str(cnf)])
            with log.open('w') as output:
                try:
                    proc = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT, timeout=limit + 10)
                    code = proc.returncode
                except subprocess.TimeoutExpired:
                    code = None
            trial = dict(supports=supports, variables=count, clauses=len(clauses),
                         cnf_sha256=sha(cnf), exit=code, command=command,
                         solver_log_sha256=sha(log))
            record['trials'].append(trial)
            if mode == 'cert-cascade' and code == 20:
                checker = folder / f'{mode}_{index}.cake.log'
                with checker.open('w') as output:
                    checked = subprocess.run(['/opt/cake_lpr/cake_lpr', str(cnf), str(proof)],
                                             stdout=output, stderr=subprocess.STDOUT, timeout=60)
                trial.update(cake_exit=checked.returncode, cake_output=checker.read_text(),
                             lrat_sha256=sha(proof), lrat_bytes=proof.stat().st_size)
                trial['certified'] = (checked.returncode == 0
                                      and 's VERIFIED UNSAT' in checker.read_text().splitlines())
            if mode == 'cert-cascade':
                for artifact in (cnf, proof, log):
                    if artifact.exists():
                        with artifact.open('rb') as source, gzip.open(str(artifact) + '.gz', 'wb') as target:
                            shutil.copyfileobj(source, target)
            if code == 10:
                tables = cascade.decode(cascade.read_model(log.read_text()), K, len(supports))
                P = 1 << n
                signals = [[(x >> v) & 1 for x in range(P)] for v in range(n)]
                for support, table in zip(supports, tables):
                    signals.append([(table >> sum((int(x == 0) if feedback and s == n + 2 else signals[s][x]) << j
                                                   for j, s in enumerate(support))) & 1
                                    for x in range(P)])
                if feedback:
                    signals.append([int(x == 0) for x in range(P)])
                options = []
                for subset in itertools.combinations(range(len(signals)), K):
                    codes = [sum(signals[s][x] << j for j, s in enumerate(subset)) for x in range(P)]
                    frequencies = {c: codes.count(c) for c in set(codes)}
                    options.append((subset, codes, frequencies))
                nodes = []
                for q in range(P):
                    subset, codes, frequencies = next(item for item in options if item[2][item[1][q]] == 1
                                                     and not (feedback and q == 0 and any(s > n for s in item[0])))
                    pins = [n + 1 if feedback and s == n + 2 else
                            s if s < n else n + 1 + P + s - n for s in subset]
                    nodes.append((pins, 1 << codes[q]))
                for support, table in zip(supports, tables):
                    nodes.append(([n + 1 if feedback and s == n + 2 else
                                   s if s < n else n + 1 + P + s - n for s in support], table))
                emit_and_verify(nodes)
                record.update(answer='SAT', architecture='two helpers with paid-output dependency' if feedback
                              else 'two cascaded helpers', supports=supports,
                              tables=[hex(table) for table in tables])
                return save()
        if mode == 'cert-cascade' and len(record['trials']) == len(configurations) and all(
                trial.get('certified') for trial in record['trials']):
            record.update(answer='CERTIFIED_CASCADE_UNSAT',
                          scope='two helpers, second reads first and K-1 primary inputs; all overlap classes')
        else:
            record.update(answer='UNRESOLVED', scope='construction search; output-to-output wiring not covered')
        return save()

    if mode in ('isolation', 'cert-isolation'):
        import isolation_multi as isolation
        if extra < 1 or n != K + 2:
            raise ValueError('support-class enumeration requires positive helper count and n=K+2')
        record['isolation_encoder_sha256'] = sha('/root/isolation_multi.py')
        edges = list(itertools.combinations(range(n), 2))
        representatives = {}
        # A K-input support omits two inputs. Input renaming fixes the first omitted pair.
        # Canonical multigraphs classify omitted pairs up to input permutation.
        permutations = list(itertools.permutations(range(n)))
        for tail in itertools.combinations_with_replacement(edges, extra - 1):
            missing = ((0, 1),) + tail
            signature = min(tuple(sorted(tuple(sorted((p[a], p[b]))) for a, b in missing))
                            for p in permutations)
            representatives.setdefault(signature, missing)
        deadline = start + seconds
        record['support_classes'] = len(representatives)
        record['trials'] = []
        for index, missing in enumerate(representatives.values()):
            remaining = deadline - time.monotonic()
            if remaining <= 2:
                break
            supports = [[v for v in range(n) if v not in edge] for edge in missing]
            count, clauses = isolation.isolation_cnf(K, n, supports)
            cnf = folder / f'isolation_{index}.cnf'
            cnf.write_text(isolation.dimacs(count, clauses))
            log = folder / f'isolation_{index}.log'
            limit = min(20, max(1, int(deadline - time.monotonic())))
            proof = folder / f'isolation_{index}.lrat'
            command = ['/opt/cadical/build/cadical', '-t', str(limit), '--seed=1']
            command += (['--lrat', '--binary=false', str(cnf), str(proof)]
                        if mode == 'cert-isolation' else [str(cnf)])
            with log.open('w') as output:
                try:
                    proc = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT, timeout=limit + 10)
                    code = proc.returncode
                except subprocess.TimeoutExpired:
                    code = None
            trial = dict(supports=supports, variables=count, clauses=len(clauses),
                         cnf_sha256=sha(cnf), exit=code, seconds_limit=limit)
            record['trials'].append(trial)
            if mode == 'cert-isolation' and code == 20:
                checker = folder / f'isolation_{index}.cake.log'
                with checker.open('w') as output:
                    checked = subprocess.run(['/opt/cake_lpr/cake_lpr', str(cnf), str(proof)],
                                             stdout=output, stderr=subprocess.STDOUT, timeout=60)
                trial.update(cake_exit=checked.returncode, cake_output=checker.read_text(),
                             lrat_sha256=sha(proof), solver_log_sha256=sha(log))
                trial['certified'] = (checked.returncode == 0
                                      and 's VERIFIED UNSAT' in checker.read_text().splitlines())
                for artifact in (cnf, proof, log):
                    with artifact.open('rb') as source, gzip.open(str(artifact) + '.gz', 'wb') as target:
                        shutil.copyfileobj(source, target)
            if code == 10:
                tables = isolation.decode(isolation.read_model(log.read_text()), K, extra)
                P = 1 << n
                signals = [[(x >> v) & 1 for x in range(P)] for v in range(n)]
                signals += [[(table >> isolation.proj(x, support)) & 1 for x in range(P)]
                            for support, table in zip(supports, tables)]
                options = []
                for subset in itertools.combinations(range(n + extra), K):
                    codes = [sum(signals[s][x] << j for j, s in enumerate(subset)) for x in range(P)]
                    frequencies = {c: codes.count(c) for c in set(codes)}
                    options.append((subset, codes, frequencies))
                nodes = []
                for q in range(P):
                    subset, codes, frequencies = next(item for item in options if item[2][item[1][q]] == 1)
                    pins = [s if s < n else n + 1 + P + s - n for s in subset]
                    nodes.append((pins, 1 << codes[q]))
                nodes += list(zip(supports, tables))
                emit_and_verify(nodes)
                record.update(answer='SAT', architecture=f'{extra} input-only helpers; depth two',
                              supports=supports, tables=[hex(table) for table in tables])
                return save()
        if mode == 'cert-isolation' and len(record['trials']) == len(representatives) and all(
                trial.get('certified') for trial in record['trials']):
            record.update(answer='CERTIFIED_DEPTH2_LOWER', depth2_lower=(1 << n) + extra + 1,
                          scope='all input-only helper support classes at this helper count; depth-two bound')
        else:
            record['answer'] = 'UNRESOLVED'
            record['scope'] = 'bounded construction search only; no global impossibility claim'
        return save()

    if mode == 'upper':
        # Equal-sized distinct subset labels identify each selector assignment.
        raw = 2
        selectors = n - raw
        label_size = K - raw
        helpers = label_size
        while len(list(itertools.combinations(range(helpers), label_size))) < 1 << selectors:
            helpers += 1
        labels = list(itertools.combinations(range(helpers), label_size))[:1 << selectors]
        P = 1 << n
        nodes = []
        for x in range(P):
            pins = list(range(raw)) + [n + 1 + P + i for i in labels[x >> raw]]
            row = (x & ((1 << raw) - 1)) | (((1 << label_size) - 1) << raw)
            nodes.append((pins, 1 << row))
        for i in range(helpers):
            pins = list(range(raw, n)) + [n] * (K - selectors)
            table = sum(1 << row for row in range(1 << K)
                        if i in labels[row & ((1 << selectors) - 1)])
            nodes.append((pins, table))
        emit_and_verify(nodes)
        record.update(answer='VERIFIED_UPPER', extra=helpers)
        return save()

    plant = None
    if isolation_reduction and mode == 'padded33':
        known = Path('/results/0ebaf05eb44f9a3c_K4_n5_e1_helper-search_t60/result.json')
        witness = json.loads(known.read_text())
        rows = witness['network'].splitlines()
        header = next(i for i, row in enumerate(rows) if row.startswith('.names ') and row.endswith(' h0'))
        table = 0
        for row in rows[header + 1:]:
            if row.startswith('.'):
                break
            pattern = row.split()[0]
            index = sum(int(bit) << i for i, bit in enumerate(pattern))
            table |= 1 << index
        xor_table = sum(1 << row for row in range(1 << K) if (row & 1) != ((row >> 1) & 1))
        P = 1 << n
        plant = {'tables': [table, xor_table, xor_table],
                 'pins': [list(range(K)), [n + 1, 0] + [n] * (K - 2),
                          [n + 1 + P + 1, 1] + [n] * (K - 2)]}
        record['control'] = 'known decoder padded with output-to-helper-to-helper chain'
    if helper_reduction and mode.startswith('case'):
        first_helpers = int(mode.split('-')[0][4:])
        plant = {'first_output_helpers': first_helpers}
        record['first_output_helpers'] = first_helpers
        record['scope'] = 'conditional helper-order case; combine every case for a global bound'
    if helper_reduction and mode.endswith('known130'):
        known = Path('/results/301c2ca9ab15eaf2_K5_n7_e2_cascade_t30_da67ba4ab98f/result.json')
        witness = json.loads(known.read_text())
        if witness['answer'] != 'SAT' or witness['nodes'] != 130:
            raise ValueError('missing known 130-node construction')
        P = 1 << n
        plant = {**(plant or {}), 'tables': [int(value, 16) for value in witness['tables']],
                 'pins': [[signal if signal < n else n + 1 + P + signal - n for signal in support]
                          for support in witness['supports']]}
        record['planted_network_sha256'] = witness['network_sha256']
    if mode in ('chain', 'broken-chain'):
        if (K, n, extra) != (3, 3, 2):
            raise ValueError('chain control requires K=3,n=3,extra=2')
        P = 1 << n
        plant = [(list(range(n)), 1 << i) for i in range(P)]
        xor_table = sum(1 << row for row in range(8) if (row & 1) != ((row >> 1) & 1))
        plant += [([n + 1, 0, n], xor_table), ([n + 1 + P, 0, n], xor_table)]
        plant[1] = ([n + 1 + P + 1, 1, 2], 1)
        if mode == 'broken-chain':
            plant[1], plant[2] = plant[2], plant[1]
    cnf = folder / 'instance.cnf'
    before = time.monotonic()
    nv, nc, meta = direct.build(str(cnf), K, n, extra, plant)
    if symmetric:
        record['normalization'] = meta['normalization']
        record['base_encoder_sha256'] = sha('/root/isolation_bound.py')
    record.update(variables=nv, clauses=nc, cnf_sha256=sha(cnf),
                  encode_seconds=round(time.monotonic() - before, 3))
    volume.commit()
    proof = folder / 'proof.lrat'
    log = folder / 'solver.log'
    command = ['/opt/cadical/build/cadical', '-t', str(seconds), '--seed=1',
               '--lrat', '--binary=false', str(cnf), str(proof)]
    with log.open('w') as output:
        try:
            proc = subprocess.run(command, stdout=output, stderr=subprocess.STDOUT, timeout=seconds + 30)
            code = proc.returncode
        except subprocess.TimeoutExpired:
            code = None
    record.update(solver_command=command, solver_exit=code, solver_log_sha256=sha(log))
    if code == 10:
        nodes, order = direct.decode(direct.read_model(log.read_text()), meta)
        emit_and_verify(nodes)
        record['answer'] = 'SAT'
    elif code == 20:
        checker = folder / 'cake_lpr.log'
        with checker.open('w') as output:
            checked = subprocess.run(['/opt/cake_lpr/cake_lpr', str(cnf), str(proof)],
                                     stdout=output, stderr=subprocess.STDOUT, timeout=120)
        record.update(cake_exit=checked.returncode, cake_output=checker.read_text(),
                      lrat_sha256=sha(proof), lrat_bytes=proof.stat().st_size)
        record['answer'] = ('CERTIFIED_UNSAT' if checked.returncode == 0
                            and 's VERIFIED UNSAT' in checker.read_text().splitlines() else 'CHECKER_REFUSAL')
    else:
        record['answer'] = 'UNKNOWN' if code in (None, 0) else 'ERROR'
    for path in (cnf, proof, log):
        if path.exists():
            with path.open('rb') as source, gzip.open(str(path) + '.gz', 'wb', compresslevel=3) as target:
                shutil.copyfileobj(source, target)
    return save()


@app.local_entrypoint()
def main(stage: str = 'qualify', k: int = 3, extra: int = 2, seconds: int = 300):
    if stage == 'qualify':
        jobs = [(3, 3, 2, 30, 'chain'), (3, 3, 2, 30, 'broken-chain'),
                (2, 3, 0, 60, 'search')]
        expected = ['SAT', 'CERTIFIED_UNSAT', 'CERTIFIED_UNSAT']
    elif stage == 'compact-qualify':
        jobs = [(3, 3, 2, 30, 'compact-chain'), (3, 3, 2, 30, 'compact-broken-chain'),
                (2, 3, 0, 60, 'compact-search'), (3, 5, 2, 90, 'compact-search')]
        expected = ['SAT', 'CERTIFIED_UNSAT', 'CERTIFIED_UNSAT', 'CERTIFIED_UNSAT']
    elif stage == 'reduced-qualify':
        jobs = [(4, 5, 1, 90, 'reduced-search'), (3, 5, 2, 90, 'reduced-search')]
        expected = ['SAT', 'CERTIFIED_UNSAT']
    elif stage == 'helper-qualify':
        jobs = [(4, 5, 1, 60, 'helper-search'), (3, 5, 2, 90, 'helper-search'),
                (5, 7, 2, 90, 'helper-known130')]
        expected = ['SAT', 'CERTIFIED_UNSAT', 'SAT']
    elif stage == 'helper-case-qualify':
        jobs = [(4, 5, 1, 60, 'helper-case1'), (3, 5, 2, 60, 'helper-case1'),
                (3, 5, 2, 60, 'helper-case2'), (5, 7, 2, 90, 'helper-case2-known130')]
        expected = ['SAT', 'CERTIFIED_UNSAT', 'CERTIFIED_UNSAT', 'SAT']
    elif stage == 'iso-qualify':
        jobs = [(4, 5, 1, 60, 'iso-search'), (3, 5, 2, 60, 'iso-search'),
                (5, 7, 2, 60, 'iso-known130'), (4, 5, 3, 60, 'iso-padded33')]
        expected = ['SAT', 'CERTIFIED_UNSAT', 'SAT', 'SAT']
    elif stage == 'sym-qualify':
        jobs = [(4, 5, 1, 60, 'sym-search'), (3, 5, 2, 60, 'sym-search')]
        expected = ['SAT', 'CERTIFIED_UNSAT']
    elif stage == 'upper':
        jobs = [(K, K + 2, 0, 30, 'upper') for K in (3, 4, 5)]
        expected = ['VERIFIED_UPPER'] * 3
    elif stage == 'cascade-qualify':
        jobs = [(3, 3, 2, 30, 'cascade')]
        expected = ['SAT']
    elif stage == 'cascade':
        jobs = [(k, k + 2, 2, seconds, 'cascade')]
        expected = None
    elif stage == 'cert-cascade':
        jobs = [(k, k + 2, 2, seconds, 'cert-cascade')]
        expected = None
    elif stage == 'feedback-qualify':
        jobs = [(3, 3, 2, 30, 'feedback')]
        expected = ['SAT']
    elif stage == 'feedback':
        jobs = [(k, k + 2, 2, seconds, 'feedback')]
        expected = None
    elif stage == 'cascade3':
        jobs = [(k, k + 2, 3, seconds, 'cascade3')]
        expected = None
    elif stage == 'search':
        jobs = [(k, k + 2, extra, seconds, 'search')]
        expected = None
    elif stage == 'compact-search':
        jobs = [(k, k + 2, extra, seconds, 'compact-search')]
        expected = None
    elif stage == 'reduced-search':
        jobs = [(k, k + 2, extra, seconds, 'reduced-search')]
        expected = None
    elif stage == 'helper-search':
        jobs = [(k, k + 2, extra, seconds, 'helper-search')]
        expected = None
    elif stage == 'iso-search':
        jobs = [(k, k + 2, extra, seconds, 'iso-search')]
        expected = None
    elif stage == 'sym-search':
        jobs = [(k, k + 2, extra, seconds, 'sym-search')]
        expected = None
    elif stage == 'helper-cases':
        jobs = [(k, k + 2, extra, seconds, f'helper-case{r}') for r in range(1, extra + 1)]
        expected = None
    elif stage == 'cert-isolation2':
        jobs = [(k, k + 2, 2, seconds, 'cert-isolation2')]
        expected = ['CERTIFIED_DEPTH2_LOWER']
    elif stage == 'isolation':
        jobs = [(k, k + 2, extra, seconds, 'isolation')]
        expected = None
    elif stage == 'cert-isolation':
        jobs = [(k, k + 2, extra, seconds, 'cert-isolation')]
        expected = None
    else:
        raise ValueError('unknown stage')
    results_dir = HERE / 'results'
    results_dir.mkdir(exist_ok=True)
    for index, job in enumerate(jobs):
        record = experiment.remote(*job)
        (results_dir / (record['key'] + '.json')).write_text(json.dumps(record, indent=2))
        if 'network' in record:
            (results_dir / (record['key'] + '.blif')).write_text(record['network'])
        print(json.dumps({key: record.get(key) for key in
                          ('key', 'K', 'n', 'extra', 'answer', 'nodes', 'levels', 'wall_seconds',
                           'variables', 'clauses', 'cnf_sha256', 'cached')}), flush=True)
        if expected is not None and record['answer'] != expected[index]:
            raise RuntimeError(f'qualification failed: expected {expected[index]}, got {record["answer"]}')
        if stage == 'helper-cases' and record['answer'] == 'SAT':
            break
