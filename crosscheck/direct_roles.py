#!/usr/bin/env python3
"""Direct circuit encoding with node roles fixed by Lemma 1 only.

Lemma 1 of the paper is immediate: every output depends on all n > K inputs, so it is computed by a node, and
distinct minterms are distinct nodes. This encoder uses exactly that and nothing else from the paper: nodes
0 .. 2^n - 1 compute the minterms 0 .. 2^n - 1 (their values at every pattern are therefore known constants), and
with EXTRA = 1 one further node Y has a free truth table. Every node has K pins, each selecting an input, the
constant 0 or another node; the build order is free, encoded by precedence variables with transitivity, and a
pin may select a node only if that node precedes the reader. Outputs may read Y and each other; Y may read
outputs. Lemmas 2 and 3 of the paper, and the encoder built from them, are the things this encoding tests.

Clauses are streamed to the file as they are generated, so memory stays small for large instances. Pins are
constrained to non-decreasing signal order (a pure symmetry of pin labels) with a linear prefix encoding.

    python3 direct_roles.py OUT.cnf K n EXTRA [--solve CADICAL]     EXTRA is 0 (2^n nodes) or 1 (2^n + 1 nodes)
"""
import itertools
import subprocess
import sys

HEADER_WIDTH = 40


class Writer:
    def __init__(self, path):
        self.handle = open(path, 'w', newline='\n')
        self.handle.write(' ' * HEADER_WIDTH + '\n')
        self.nv = 0
        self.nc = 0

    def new(self):
        self.nv += 1
        return self.nv

    def clause(self, lits):
        self.handle.write(' '.join(map(str, lits)) + ' 0\n')
        self.nc += 1

    def close(self):
        header = f'p cnf {self.nv} {self.nc}'
        self.handle.seek(0)
        self.handle.write(header + ' ' * (HEADER_WIDTH - len(header)))
        self.handle.close()


def build(path, K, n, extra):
    """Write the instance to path; return (variables, clauses, meta) with meta for decoding a model."""
    P = 1 << n
    m = P + extra
    w = Writer(path)
    new, clause = w.new, w.clause
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
        clause([-prec(a, b), -prec(b, c), prec(a, c)])
    sel, tt = [], []
    for j in range(m):
        cands = list(range(n)) + [CONST] + [node_sig(i) for i in range(m) if i != j]
        table = [new() for _ in range(1 << K)]
        tt.append(table)
        sel_j = []
        for p in range(K):
            s_vars = {s: new() for s in cands}
            sel_j.append(s_vars)
            clause(list(s_vars.values()))  # at least one signal on the pin
            vals = list(s_vars.values())
            for a, b in itertools.combinations(vals, 2):  # at most one
                clause([-a, -b])
            for s, sv in s_vars.items():
                if s > CONST:
                    clause([-sv, prec(s - n - 1, j)])  # a read node is built first
        # pins in non-decreasing candidate order: le[p][i] <-> (pin p selects a candidate of index <= i)
        for p in range(K - 1):
            le = []
            for i, s in enumerate(cands):
                v = new()
                le.append(v)
                prev = le[i - 1] if i else None
                clause([-sel_j[p][s], v])
                if prev is not None:
                    clause([-prev, v])
                    clause([-v, sel_j[p][s], prev])
                else:
                    clause([-v, sel_j[p][s]])
                clause([-sel_j[p + 1][s], v])  # pin p+1 at index i forces pin p at index <= i
        sel.append(sel_j)
        pv_j = []  # pin values at every pattern
        for p in range(K):
            pv_px = [new() for _ in range(P)]
            pv_j.append(pv_px)
            for s, sv in sel_j[p].items():
                for x in range(P):
                    kind, wv = val(s, x)
                    if kind == 'const':
                        clause([-sv, pv_px[x] if wv else -pv_px[x]])
                    else:
                        clause([-sv, -pv_px[x], wv])
                        clause([-sv, pv_px[x], -wv])
        for x in range(P):
            if j < P:
                own_kind, own = 'const', (1 if x == j else 0)
            else:
                own_kind, own = 'var', vy[x]
            for t in range(1 << K):
                guard = [pv_j[p][x] if not (t >> p) & 1 else -pv_j[p][x] for p in range(K)]
                if own_kind == 'const':
                    clause(guard + [table[t] if own else -table[t]])
                else:
                    clause(guard + [-own, table[t]])
                    clause(guard + [own, -table[t]])
    w.close()
    return w.nv, w.nc, {'K': K, 'n': n, 'm': m, 'sel': sel, 'tt': tt, 'before': before}


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
                    bit = value[s - n - 1]
                idx |= bit << p
            value[j] = (table >> idx) & 1
        for i in range(P):
            bad += value[i] != (1 if x == i else 0)
    return bad


def read_model(stdout):
    model = {}
    for line in stdout.splitlines():
        if line.startswith('v'):
            for lit in map(int, line.split()[1:]):
                if lit:
                    model[abs(lit)] = lit > 0
    return model


def main():
    out, K, n, extra = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    nv, nc, meta = build(out, K, n, extra)
    print(f'K={K} n={n} nodes={meta["m"]}: {nv} variables, {nc} clauses', flush=True)
    if '--solve' not in sys.argv:
        return 0
    run = subprocess.run([sys.argv[sys.argv.index('--solve') + 1], '-q', out], capture_output=True, text=True)
    if run.returncode == 20:
        print('UNSAT: no such network')
        return 20
    if run.returncode != 10:
        print('solver exit', run.returncode)
        return run.returncode
    nodes, order = decode(read_model(run.stdout), meta)
    bad = simulate(nodes, order, K, n)
    print(f'SAT: network decoded; simulation mismatches {bad}; build order {order}')
    names = [f'x{s}' for s in range(n)] + ['0'] + [f'o{j}' for j in range(1 << n)] + ['Y']
    for j in order:
        fanin, table = nodes[j]
        print(f'  {names[n + 1 + j]} = LUT{K}(' + ', '.join(names[s] for s in fanin) + f') table 0x{table:0{max(1, (1 << K) // 4)}x}')
    return 10 if bad == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
