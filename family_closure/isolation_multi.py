#!/usr/bin/env python3
"""The (K+2)-input decoder with LUT-K nodes, for every K: the isolation instance with two shared LUTs.

A network of 2^n + 2 LUT-K nodes in the shape of the paper's 258-LUT netlist: two shared LUTs Y_0, Y_1, each reading
K inputs, and one LUT per output, reading K signals among the inputs and the shared LUTs. The output for pattern q
is its minterm exactly when q's code under its K signals is unique among the 2^n patterns (the signals isolate q).
`isolation_cnf` writes the question "do two tables exist under which every pattern is isolated by one shared LUT and
K-1 inputs or by both shared LUTs and K-2 inputs?" as CNF over the two tables; `classes` lists the support pairs
up to input permutation (only the overlap matters). A model is decoded by `decode`, turned into a netlist by
`network`, and that netlist is simulated on every pattern by `simulate`, which shares nothing with the encoder.

    python3 family.py K n [PREFIX]   print the classes and the CNF sizes; with PREFIX, write PREFIX_<overlap>.cnf
"""
import itertools
import sys


def proj(x, support):
    return sum(((x >> v) & 1) << j for j, v in enumerate(support))


def classes(K, n):
    """Support pairs for two shared K-input LUTs over n inputs, one per overlap, widest union first."""
    return [[list(range(K)), list(range(K - o, 2 * K - o))] for o in range(max(0, 2 * K - n), K + 1)]


def isolation_cnf(K, n, supports):
    """Variables 1 .. 2^K per shared LUT hold its table (bit m is the value at projection m of its support)."""
    P = 1 << K
    count = 0

    def new():
        nonlocal count
        count += 1
        return count

    tables = [[new() for _ in range(P)] for _ in supports]
    value = [[tables[i][proj(x, s)] for x in range(1 << n)] for i, s in enumerate(supports)]
    clauses = [[-t[0]] for t in tables]  # a complemented shared LUT isolates the same points
    differ = {}

    def differs(a, b):
        if a == b:
            return None
        key = (min(a, b), max(a, b))
        if key not in differ:
            e = new()
            clauses.append([-e, a, b])
            clauses.append([-e, -a, -b])
            differ[key] = e
        return differ[key]

    k = len(supports)
    groups = [(list(shared), K - size)
              for size in range(1, min(k, K) + 1)
              for shared in itertools.combinations(range(k), size)]
    for q in range(1 << n):
        options = []
        for shared, raw in groups:
            for kept in itertools.combinations(range(n), raw):
                free = [v for v in range(n) if v not in kept]
                z = new()
                ok = True
                for bits in range(1, 1 << len(free)):
                    x = q ^ sum(1 << v for j, v in enumerate(free) if (bits >> j) & 1)
                    lits = [d for d in (differs(value[i][x], value[i][q]) for i in shared) if d is not None]
                    if not lits:
                        ok = False
                        break
                    clauses.append([-z] + lits)
                if ok:
                    options.append(z)
        clauses.append(options)
    return count, clauses


def dimacs(count, clauses):
    return f'p cnf {count} {len(clauses)}\n' + ''.join(' '.join(map(str, c)) + ' 0\n' for c in clauses)


def read_model(stdout):
    model = {}
    for line in stdout.splitlines():
        if line.startswith('v'):
            for lit in map(int, line.split()[1:]):
                if lit:
                    model[abs(lit)] = lit > 0
    return model


def decode(model, K, k=2):
    P = 1 << K
    return [sum(1 << m for m in range(P) if model.get(P * i + m + 1)) for i in range(k)]


def network(K, n, supports, tables):
    """Two-level netlist: shared LUTs y0, y1 over inputs i0..i{n-1}; output m{q} over the lexicographically first
    K-subset of the n + 2 signals that isolates q. Raises when a pattern is not isolated."""
    k = len(supports)
    signal = [[(x >> v) & 1 for x in range(1 << n)] for v in range(n)]
    signal += [[(tt >> proj(x, s)) & 1 for x in range(1 << n)] for s, tt in zip(supports, tables)]
    names = [f'i{v}' for v in range(n)] + [f'y{j}' for j in range(k)]
    codes = {}
    for subset in itertools.combinations(range(n + k), K):
        column = [sum(signal[s][x] << j for j, s in enumerate(subset)) for x in range(1 << n)]
        counts = {}
        for c in column:
            counts[c] = counts.get(c, 0) + 1
        codes[subset] = (column, counts)
    lines = ['.model dec', '.inputs ' + ' '.join(names[:n]), '.outputs ' + ' '.join(f'm{q}' for q in range(1 << n))]
    for j, (support, tt) in enumerate(zip(supports, tables)):
        lines.append('.names ' + ' '.join(names[v] for v in support) + f' y{j}')
        lines += [''.join(str((m >> b) & 1) for b in range(len(support))) + ' 1'
                  for m in range(1 << len(support)) if (tt >> m) & 1]
    for q in range(1 << n):
        subset = next((s for s, (column, counts) in codes.items() if counts[column[q]] == 1), None)
        if subset is None:
            raise RuntimeError(f'pattern {q} is not isolated')
        lines.append('.names ' + ' '.join(names[s] for s in subset) + f' m{q}')
        lines.append(''.join(str(signal[s][q]) for s in subset) + ' 1')
    lines.append('.end')
    return '\n'.join(lines) + '\n'


def simulate(blif, n):
    """Evaluate the netlist on every pattern; return (mismatches, luts, levels). Output m{q} must be minterm q."""
    nodes = []  # (output name, input names, set of accepted cubes)
    lines = [l.strip() for l in blif.splitlines() if l.strip() and not l.startswith('#')]
    i = 0
    while i < len(lines):
        parts = lines[i].split()
        if parts[0] == '.names':
            cubes = []
            i += 1
            while i < len(lines) and not lines[i].startswith('.'):
                cube, out = lines[i].split()
                assert out == '1'
                cubes.append(cube)
                i += 1
            nodes.append((parts[-1], parts[1:-1], cubes))
        else:
            i += 1
    level = {f'i{v}': 0 for v in range(n)}
    mism = 0
    for x in range(1 << n):
        val = {f'i{v}': (x >> v) & 1 for v in range(n)}
        for out, ins, cubes in nodes:
            word = ''.join(str(val[s]) for s in ins)
            val[out] = int(any(all(c == '-' or c == w for c, w in zip(cube, word)) for cube in cubes))
        for q in range(1 << n):
            if val[f'm{q}'] != int(x == q):
                mism += 1
    for out, ins, _ in nodes:
        level[out] = 1 + max(level[s] for s in ins)
    return mism, len(nodes), max(level[f'm{q}'] for q in range(1 << n))


if __name__ == '__main__':
    K, n = int(sys.argv[1]), int(sys.argv[2])
    for supports in classes(K, n):
        count, clauses = isolation_cnf(K, n, supports)
        print(supports, count, 'variables', len(clauses), 'clauses')
        if len(sys.argv) > 3:
            overlap = len(set(supports[0]) & set(supports[1]))
            with open(f'{sys.argv[3]}_{overlap}.cnf', 'w', newline='\n') as handle:
                handle.write(dimacs(count, clauses))
