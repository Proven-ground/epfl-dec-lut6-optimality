#!/usr/bin/env python3
"""Direct circuit encoding with node roles fixed by Lemma 1 only.

Lemma 1 of the paper is immediate: every output depends on all n > K inputs, so it is computed by a node, and
distinct minterms are distinct nodes. This encoder uses exactly that and nothing else from the paper: nodes
0 .. 2^n - 1 compute the minterms 0 .. 2^n - 1 (their values at every pattern are therefore known constants), and
with EXTRA arbitrary additional nodes have free truth tables. Every node has K pins, each selecting an input, the
constant 0 or another node; the build order is free, encoded by precedence variables with transitivity, and a
pin may select a node only if that node precedes the reader. Outputs may read Y and each other; Y may read
outputs. Lemmas 2 and 3 of the paper, and the encoder built from them, are the things this encoding tests.

This equivalent compact encoding uses linear one-hot counters and omits implicit known-zero pin cases.
Clauses are streamed to the file as they are generated, so memory stays small for large instances. Pins are
constrained to non-decreasing signal order (a pure symmetry of pin labels) with a linear prefix encoding.

    python3 direct_roles.py OUT.cnf K n EXTRA [--solve CADICAL]     EXTRA is any nonnegative number of non-output nodes
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


def canonical(fanin, table, K):
    """The same LUT with its pins in non-decreasing signal order and its table permuted to match."""
    perm = sorted(range(K), key=lambda p: fanin[p])
    new_table = 0
    for t in range(1 << K):
        old = sum(((t >> p) & 1) << perm[p] for p in range(K))
        if (table >> old) & 1:
            new_table |= 1 << t
    return [fanin[perm[p]] for p in range(K)], new_table


def build(path, K, n, extra, plant=None):
    """Write the instance to path; return (variables, clauses, meta) with meta for decoding a model.
    plant, a list of (fanin, table) per node, adds unit clauses fixing that network (pins canonicalised), so the
    instance asks whether the encoding admits it."""
    if not 1 <= K < n + 1 or extra < 0:
        raise ValueError("invalid LUT size, input count or extra-node count")
    P = 1 << n
    m = P + extra
    w = Writer(path)
    new, clause = w.new, w.clause
    CONST = n
    node_sig = lambda j: n + 1 + j
    vy = [[new() for _ in range(P)] for _ in range(extra)]

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
            # Linear at-most-one counter. The existing clause supplies at least one.
            previous = None
            for literal in vals[:-1]:
                prefix = new()
                clause([-literal, prefix])
                if previous is not None:
                    clause([-previous, prefix])
                    clause([-literal, -previous])
                previous = prefix
            if previous is not None:
                clause([-vals[-1], -previous])
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
            selectors = sel_j[p]
            primaries = [(s, sv) for s, sv in selectors.items() if s < n]
            helpers = [(sv, vy[s - n - 1 - P]) for s, sv in selectors.items() if s >= n + 1 + P]
            for x in range(P):
                ones = [sv for s, sv in primaries if (x >> s) & 1]
                output_at_x = selectors.get(node_sig(x))
                if output_at_x is not None:
                    ones.append(output_at_x)
                # Exactly one signal is selected. A true pin must select either a
                # known-one signal or a helper whose value is then constrained below.
                clause([-pv_px[x]] + ones + [sv for sv, values in helpers])
                for sv in ones:
                    clause([-sv, pv_px[x]])
                for sv, values in helpers:
                    clause([-sv, -pv_px[x], values[x]])
                    clause([-sv, pv_px[x], -values[x]])
        for x in range(P):
            if j < P:
                own_kind, own = 'const', (1 if x == j else 0)
            else:
                own_kind, own = 'var', vy[j - P][x]
            for t in range(1 << K):
                guard = [pv_j[p][x] if not (t >> p) & 1 else -pv_j[p][x] for p in range(K)]
                if own_kind == 'const':
                    clause(guard + [table[t] if own else -table[t]])
                else:
                    clause(guard + [-own, table[t]])
                    clause(guard + [own, -table[t]])
    if n > K and extra:
        # Lemma 2: every minterm output reads a non-output node. The first
        # non-output node consequently precedes every output and reads inputs only.
        # Relabel helpers in their build order, then permute primary inputs to pad
        # this first helper's support to 0..K-1. Translate inputs by the earliest
        # output's pattern so that output 0 is earliest. Negating the first helper
        # is absorbed by its readers, permitting table bit zero to be cleared.
        for a in range(P, m):
            for b in range(a + 1, m):
                clause([prec(a, b)])
        for output in range(P):
            clause([prec(P, output)])
            choices = [sv for pin in sel[output] for signal, sv in pin.items()
                       if signal >= n + 1 + P]
            clause(choices)
        for output in range(1, P):
            clause([prec(0, output)])
        for pin in range(K):
            clause([sel[P][pin][pin]])
        clause([-tt[P][0]])
    if plant is not None:
        if len(plant) != m:
            raise ValueError(f'planted network has {len(plant)} nodes, the instance {m}')
        for j, (fanin, table) in enumerate(plant):
            fanin, table = canonical(fanin, table, K)
            for p, s in enumerate(fanin):
                if s not in sel[j][p]:
                    raise ValueError(f'node {j} pin {p} reads signal {s}, which it cannot select')
                clause([sel[j][p][s]])
            for t in range(1 << K):
                clause([tt[j][t] if (table >> t) & 1 else -tt[j][t]])
    w.close()
    return w.nv, w.nc, {'K': K, 'n': n, 'm': m, 'sel': sel, 'tt': tt, 'before': before}


def decode(model, meta):
    K, n, m = meta['K'], meta['n'], meta['m']
    nodes = []
    for j in range(m):
        fanin = []
        for p in range(K):
            chosen = [s for s, sv in meta['sel'][j][p].items() if model.get(sv)]
            if len(chosen) != 1:
                raise ValueError(f'model selects {len(chosen)} signals for pin {p} of node {j}')
            fanin.append(chosen[0])
        nodes.append((fanin, sum(1 << t for t in range(1 << K) if model.get(meta['tt'][j][t]))))

    def earlier(a, b):
        key = (min(a, b), max(a, b))
        return bool(model.get(meta['before'][key])) == (a < b)
    order = sorted(range(m), key=lambda j: sum(earlier(i, j) for i in range(m) if i != j))
    return nodes, order


def topological(nodes, n, K):
    """A build order computed from the decoded fanins alone, or None when the network is not a circuit: a node with
    other than K pins, a table wider than 2^K bits, a pin naming a signal that does not exist, or a cycle."""
    items = nodes.items() if isinstance(nodes, dict) else enumerate(nodes)
    deps = {}
    for j, (fanin, table) in items:
        if len(fanin) != K or not 0 <= table < 1 << (1 << K) or any(s < 0 for s in fanin):
            return None
        deps[j] = {s - n - 1 for s in fanin if s > n}
    if any(d not in deps for ds in deps.values() for d in ds):
        return None
    order, done = [], set()
    while len(order) < len(deps):
        ready = [j for j in deps if j not in done and deps[j] <= done]
        if not ready:
            return None
        for j in sorted(ready):
            order.append(j)
            done.add(j)
    return order


def simulate(nodes, order, K, n):
    """Independent check: evaluate the decoded network on every pattern; node i < 2^n must be minterm i.
    The evaluation order is recomputed from the fanins, so the check does not trust the solver's build order.
    Returns the number of (pattern, output) pairs that differ from the minterm, or 'invalid' when the decoded nodes
    do not form a circuit (see topological); a caller treats anything but 0 as a failure."""
    order = topological(nodes, n, K)
    if order is None or any(i not in (nodes if isinstance(nodes, dict) else range(len(nodes))) for i in range(1 << n)):
        return 'invalid'
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
    names = [f'x{s}' for s in range(n)] + ['0'] + [f'o{j}' for j in range(1 << n)] + [f'Y{i}' for i in range(extra)]
    for j in order:
        fanin, table = nodes[j]
        print(f'  {names[n + 1 + j]} = LUT{K}(' + ', '.join(names[s] for s in fanin) + f') table 0x{table:0{max(1, (1 << K) // 4)}x}')
    return 10 if bad == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
