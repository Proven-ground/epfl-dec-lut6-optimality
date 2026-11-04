#!/usr/bin/env python3
"""The paper's reduction, parametrised by the LUT size K and the number of decoder inputs n.

Question encoded: can a decoder of n inputs (all 2^n minterms) be built from 2^n + 1 LUTs of at most K inputs,
n > K? The reduction of the paper (Lemmas 1 to 3, stated there for K = 6, n = 8) gives a necessary condition: a
function Y on K inputs and a build order of the 2^K points of its support such that every point z has a free set
F of BASE + u inputs, BASE = n - K + 1, u = 0 .. K - BASE, in which at most u other points share Y(z), all built
before z. With K = 6 and n = 8 this writes record/generator/bound.py's instance clause for clause; with K = 6 and
n = 7 it writes the stored 7-input control.

    python3 reduced_bound.py OUT.cnf K n
"""
import itertools
import sys


def write(out, K, n):
    base = n - K + 1
    assert 1 <= base <= K, 'the reduction needs K < n <= 2K - 1'
    P = 1 << K
    nv = 0
    clauses = []

    def new():
        nonlocal nv
        nv += 1
        return nv

    y = [new() for _ in range(P)]
    clauses.append([-y[0]])  # complementing Y changes nothing
    before = {}
    for a in range(P):
        for b in range(a + 1, P):
            before[(a, b)] = new()

    def prec(a, b):
        return before[(a, b)] if a < b else -before[(b, a)]

    for a, b, c in itertools.permutations(range(P), 3):  # transitivity of the build order
        clauses.append([-prec(a, b), -prec(b, c), prec(a, c)])
    same = {}

    def eq(a, b):
        key = (min(a, b), max(a, b))
        if key not in same:
            e = new()
            ya, yb = y[key[0]], y[key[1]]
            clauses.extend([[-e, -ya, yb], [-e, ya, -yb], [e, ya, yb], [e, -ya, -yb]])
            same[key] = e
        return same[key]

    def at_most(lits, k):
        if k >= len(lits):
            return
        if k == 0:
            for lit in lits:
                clauses.append([-lit])
            return
        s = [[new() for _ in range(k)] for _ in lits]
        for i, lit in enumerate(lits):
            clauses.append([-lit, s[i][0]])
            if i > 0:
                for j in range(k):
                    clauses.append([-s[i - 1][j], s[i][j]])
                for j in range(1, k):
                    clauses.append([-lit, -s[i - 1][j - 1], s[i][j]])
                clauses.append([-lit, -s[i - 1][k - 1]])

    for z in range(P):
        options = []
        for u in range(K - base + 1):
            for F in itertools.combinations(range(K), base + u):
                members = []
                for bits in range(1, 1 << len(F)):
                    x = z
                    for j, v in enumerate(F):
                        if (bits >> j) & 1:
                            x ^= 1 << v
                    members.append(x)
                c = new()
                options.append(c)
                guarded = []
                for x in members:
                    m = eq(z, x)
                    clauses.append([-c, -m, prec(x, z)])
                    g = new()
                    clauses.extend([[-g, c], [-g, m], [g, -c, -m]])
                    guarded.append(g)
                at_most(guarded, u)
        clauses.append(options)
    with open(out, 'w', newline='\n') as handle:
        handle.write(f'p cnf {nv} {len(clauses)}\n')
        handle.write(''.join(' '.join(map(str, cl)) + ' 0\n' for cl in clauses))
    return nv, len(clauses)


if __name__ == '__main__':
    print(*write(sys.argv[1], int(sys.argv[2]), int(sys.argv[3])))
