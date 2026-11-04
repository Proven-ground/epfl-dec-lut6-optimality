#!/usr/bin/env python3
"""Direct circuit encoding: does a network of m LUTs of at most K inputs compute all 2^n minterms of n inputs?

Nothing from the paper's reduction is used. A network is m nodes numbered in a topological order; node j has K
pins, each selecting one signal among the n inputs, the constant 0 (so fewer than K fanins are allowed) and the
nodes before j; node j has a free truth table of 2^K bits. Every minterm must be the function of some node. The
value of every node at every one of the 2^n input patterns is encoded, so a model is a concrete network, which
this script decodes, simulates on all patterns and checks before reporting it.

    python3 direct_bound.py OUT.cnf K n m                 write the CNF
    python3 direct_bound.py OUT.cnf K n m --solve CADICAL  write, solve, decode the model, check and print it
"""
import itertools
import subprocess
import sys


def encode(K, n, m):
    P = 1 << n
    nv = 0
    clauses = []

    def new():
        nonlocal nv
        nv += 1
        return nv

    inputs = list(range(n))
    CONST = n
    node_sig = lambda j: n + 1 + j
    # value of a signal at pattern x: constant (0/1) for inputs and CONST, a variable for nodes
    v = [[new() for _ in range(P)] for _ in range(m)]

    def val(s, x):
        """('const', 0 or 1) for an input or the constant, ('var', variable) for a node."""
        if s < n:
            return 'const', (x >> s) & 1
        if s == CONST:
            return 'const', 0
        return 'var', v[s - n - 1][x]

    sel = []
    pv = []
    tt = [[new() for _ in range(1 << K)] for _ in range(m)]
    for j in range(m):
        cands = inputs + [CONST] + [node_sig(i) for i in range(j)]
        sel_j, pv_j = [], []
        for p in range(K):
            s_vars = {s: new() for s in cands}
            sel_j.append(s_vars)
            clauses.append(list(s_vars.values()))  # at least one signal on the pin
            for a, b in itertools.combinations(s_vars.values(), 2):  # at most one
                clauses.append([-a, -b])
            pv_px = [new() for _ in range(P)]
            pv_j.append(pv_px)
            for s, sv in s_vars.items():
                for x in range(P):
                    kind, w = val(s, x)
                    if kind == 'const':
                        clauses.append([-sv, pv_px[x] if w else -pv_px[x]])
                    else:
                        clauses.append([-sv, -pv_px[x], w])
                        clauses.append([-sv, pv_px[x], -w])
        sel.append(sel_j)
        pv.append(pv_j)
        for x in range(P):
            for t in range(1 << K):
                guard = [pv_j[p][x] if not (t >> p) & 1 else -pv_j[p][x] for p in range(K)]
                clauses.append(guard + [-v[j][x], tt[j][t]])
                clauses.append(guard + [v[j][x], -tt[j][t]])
    out = [[new() for _ in range(m)] for _ in range(P)]
    for i in range(P):
        clauses.append(out[i])  # some node computes minterm i
        for j in range(m):
            for x in range(P):
                clauses.append([-out[i][j], v[j][x] if x == i else -v[j][x]])
    return nv, clauses, {'v': v, 'sel': sel, 'tt': tt, 'out': out, 'K': K, 'n': n, 'm': m}


def write(path, nv, clauses):
    with open(path, 'w', newline='\n') as handle:
        handle.write(f'p cnf {nv} {len(clauses)}\n')
        handle.write(''.join(' '.join(map(str, cl)) + ' 0\n' for cl in clauses))


def decode(model, meta):
    K, n, m = meta['K'], meta['n'], meta['m']
    nodes = []
    for j in range(m):
        fanin = []
        for p in range(K):
            chosen = [s for s, sv in meta['sel'][j][p].items() if model.get(sv)]
            assert len(chosen) == 1
            fanin.append(chosen[0])
        table = sum(1 << t for t in range(1 << K) if model.get(meta['tt'][j][t]))
        nodes.append((fanin, table))
    outputs = []
    for i in range(1 << n):
        js = [j for j in range(m) if model.get(meta['out'][i][j])]
        assert js
        outputs.append(js[0])
    return nodes, outputs


def simulate(nodes, outputs, K, n):
    """Independent check of a decoded network: every output node is its minterm on every pattern."""
    bad = 0
    for x in range(1 << n):
        value = {}
        for j, (fanin, table) in enumerate(nodes):
            idx = 0
            for p, s in enumerate(fanin):
                if s < n:
                    bit = (x >> s) & 1
                elif s == n:
                    bit = 0
                else:
                    assert s - n - 1 < j, 'fanin must precede the node'
                    bit = value[s - n - 1]
                idx |= bit << p
            value[j] = (table >> idx) & 1
        for i, j in enumerate(outputs):
            bad += value[j] != (1 if x == i else 0)
    return bad


def main():
    out, K, n, m = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    nv, clauses, meta = encode(K, n, m)
    write(out, nv, clauses)
    print(f'K={K} n={n} m={m}: {nv} variables, {len(clauses)} clauses')
    if '--solve' not in sys.argv:
        return 0
    cadical = sys.argv[sys.argv.index('--solve') + 1]
    run = subprocess.run([cadical, '-q', out], capture_output=True, text=True)
    if run.returncode == 20:
        print('UNSAT: no such network')
        return 20
    if run.returncode != 10:
        print('solver exit', run.returncode)
        return run.returncode
    model = {}
    for line in run.stdout.splitlines():
        if line.startswith('v'):
            for lit in map(int, line.split()[1:]):
                if lit:
                    model[abs(lit)] = lit > 0
    nodes, outputs = decode(model, meta)
    bad = simulate(nodes, outputs, K, n)
    print(f'SAT: network of {m} nodes decoded; simulation mismatches {bad}')
    names = [f'x{s}' for s in range(n)] + ['0'] + [f'g{j}' for j in range(m)]
    for j, (fanin, table) in enumerate(nodes):
        role = [i for i, oj in enumerate(outputs) if oj == j]
        print(f'  g{j} = LUT{K}(' + ', '.join(names[s] for s in fanin) + f') table 0x{table:0{(1 << K) // 4 or 1}x}' + (f'  minterm {role[0]}' if role else '  shared'))
    return 10 if bad == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
