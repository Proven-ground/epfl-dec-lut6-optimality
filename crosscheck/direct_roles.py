#!/usr/bin/env python3
"""Direct circuit encoding with node roles fixed by Lemma 1 only.

Lemma 1 of the paper is immediate: every output depends on all n > K inputs, so it is computed by a node, and
distinct minterms are distinct nodes. This encoder uses exactly that and nothing else from the paper: nodes
0 .. 2^n - 1 compute the minterms 0 .. 2^n - 1 (their values at every pattern are therefore known constants), and
with --extra 1 one further node Y has a free truth table. Every node has K pins, each selecting an input, the
constant 0 or another node; the build order is free, encoded by precedence variables with transitivity, and a
pin may select a node only if that node precedes the reader. Outputs may read Y and each other; Y may read
outputs. Lemmas 2 and 3 of the paper, and the encoder built from them, are the things this encoding tests.

    python3 direct_roles.py OUT.cnf K n EXTRA [--solve CADICAL]     EXTRA is 0 (2^n nodes) or 1 (2^n + 1 nodes)
"""
import itertools
import subprocess
import sys


def encode(K, n, extra):
    P = 1 << n
    m = P + extra
    nv = 0
    clauses = []

    def new():
        nonlocal nv
        nv += 1
        return nv

    CONST = n
    node_sig = lambda j: n + 1 + j
    vy = [new() for _ in range(P)] if extra else None  # values of Y

    def val(s, x):
        if s < n:
            return 'const', (x >> s) & 1
        if s == CONST:
            return 'const', 0
        j = s - n - 1
        if j < P:
            return 'const', 1 if x == j else 0
        return 'var', vy[x]

    before = {}
    for a in range(m):
        for b in range(a + 1, m):
            before[(a, b)] = new()

    def prec(a, b):
        return before[(a, b)] if a < b else -before[(b, a)]

    for a, b, c in itertools.permutations(range(m), 3):
        clauses.append([-prec(a, b), -prec(b, c), prec(a, c)])
    sel, tt = [], []
    for j in range(m):
        cands = list(range(n)) + [CONST] + [node_sig(i) for i in range(m) if i != j]
        table = [new() for _ in range(1 << K)]
        tt.append(table)
        sel_j = []
        for p in range(K):
            s_vars = {s: new() for s in cands}
            sel_j.append(s_vars)
            clauses.append(list(s_vars.values()))
            for a, b in itertools.combinations(s_vars.values(), 2):
                clauses.append([-a, -b])
            for s, sv in s_vars.items():
                if s > CONST:
                    clauses.append([-sv, prec(s - n - 1, j)])  # a read node is built first
        if K > 1:  # pins in non-decreasing signal order: a pure symmetry of the pin labels
            order = cands
            for p in range(K - 1):
                for ia, a in enumerate(order):
                    for b in order[:ia]:
                        clauses.append([-sel_j[p][a], -sel_j[p + 1][b]])
        sel.append(sel_j)
        pv_j = []  # pin values at every pattern
        for p in range(K):
            pv_px = [new() for _ in range(P)]
            pv_j.append(pv_px)
            for s, sv in sel_j[p].items():
                for x in range(P):
                    kind, w = val(s, x)
                    if kind == 'const':
                        clauses.append([-sv, pv_px[x] if w else -pv_px[x]])
                    else:
                        clauses.append([-sv, -pv_px[x], w])
                        clauses.append([-sv, pv_px[x], -w])
        for x in range(P):
            if j < P:
                own_kind, own = 'const', (1 if x == j else 0)
            else:
                own_kind, own = 'var', vy[x]
            for t in range(1 << K):
                guard = [pv_j[p][x] if not (t >> p) & 1 else -pv_j[p][x] for p in range(K)]
                if own_kind == 'const':
                    clauses.append(guard + [table[t] if own else -table[t]])
                else:
                    clauses.append(guard + [-own, table[t]])
                    clauses.append(guard + [own, -table[t]])
    return nv, clauses, {'K': K, 'n': n, 'm': m, 'sel': sel, 'tt': tt, 'before': before}


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
        nodes.append((fanin, sum(1 << t for t in range(1 << K) if model.get(meta['tt'][j][t]))))
    # a topological order from the precedence variables
    def earlier(a, b):
        key = (min(a, b), max(a, b))
        return bool(model.get(meta['before'][key])) == (a < b)
    order = sorted(range(m), key=lambda j: sum(earlier(i, j) for i in range(m) if i != j))
    return nodes, order


def simulate(nodes, order, K, n):
    """Independent check: evaluate the decoded network in its build order on every pattern; node i < 2^n must be
    minterm i. Returns the mismatch count; raises if a node reads one not yet built."""
    P = 1 << n
    bad = 0
    for x in range(P):
        value = {}
        for j in order:
            fanin, table = nodes[j]
            idx = 0
            for p, s in enumerate(fanin):
                if s < n:
                    bit = (x >> s) & 1
                elif s == n:
                    bit = 0
                else:
                    bit = value[s - n - 1]  # KeyError if not built yet
                idx |= bit << p
            value[j] = (table >> idx) & 1
        for i in range(P):
            bad += value[i] != (1 if x == i else 0)
    return bad


def main():
    out, K, n, extra = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    nv, clauses, meta = encode(K, n, extra)
    write(out, nv, clauses)
    print(f'K={K} n={n} nodes={meta["m"]}: {nv} variables, {len(clauses)} clauses')
    if '--solve' not in sys.argv:
        return 0
    run = subprocess.run([sys.argv[sys.argv.index('--solve') + 1], '-q', out], capture_output=True, text=True)
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
    nodes, order = decode(model, meta)
    bad = simulate(nodes, order, K, n)
    print(f'SAT: network decoded; simulation mismatches {bad}; build order {order}')
    names = [f'x{s}' for s in range(n)] + ['0'] + [f'o{j}' for j in range(1 << n)] + ['Y']
    for j in order:
        fanin, table = nodes[j]
        print(f'  {names[n + 1 + j]} = LUT{K}(' + ', '.join(names[s] for s in fanin) + f') table 0x{table:0{max(1, (1 << K) // 4)}x}')
    return 10 if bad == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
