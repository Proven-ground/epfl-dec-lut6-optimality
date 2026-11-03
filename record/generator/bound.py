"""Exhaustive proof that an 8-input decoder has no 6-LUT network of 257 LUTs (so 258 is optimal).

256 outputs are distinct minterms, so each needs its own LUT; 257 LUTs leave one other LUT, Y. An output LUT reading
only inputs and other outputs cannot be a minterm (6 - u inputs leave 2^(2+u) > 1 + u candidates), so Y precedes
every output and reads inputs only: a set V of at most 6. Every output therefore reads Y, 5 - u raw inputs and u
earlier outputs, leaving 3 + u free inputs F, and is q's minterm iff the points of q's F-subcube with Y = Y(q)
number at most 1 + u and are all built before q. A free input outside V doubles q's class; every such choice is
dominated by one with F inside V (its class contains the smaller class and needs a superset built first). So a
257-LUT decoder exists iff Y: {0,1}^6 -> {0,1} and a build order of the 64 points of V exist with each point z
having a (3 + u)-subcube, u = 0..3, in which at most u other points share Y(z), all built before z. This writes
that question as CNF (the order as precedence variables with transitivity); CaDiCaL answers UNSATISFIABLE.

    python bound.py OUT.cnf
"""
import itertools
import sys

N = 6
P = 1 << N
nv = 0
clauses = []


def new():
    global nv
    nv += 1
    return nv


y = [new() for _ in range(P)]
clauses.append([-y[0]])  # complementing Y changes nothing
before = {}
for a in range(P):
    for b in range(a + 1, P):
        before[(a, b)] = new()


def prec(a, b):
    """Literal: a is built before b."""
    return before[(a, b)] if a < b else -before[(b, a)]


for a, b, c in itertools.permutations(range(P), 3):  # transitivity of the total order
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
    """Sequential counter: at most k of lits true."""
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
    for u in range(4):
        for F in itertools.combinations(range(N), 3 + u):
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
                clauses.append([-c, -m, prec(x, z)])  # a class member is built before z
                g = new()  # g <-> (c and m), counted
                clauses.extend([[-g, c], [-g, m], [g, -c, -m]])
                guarded.append(g)
            at_most(guarded, u)
    clauses.append(options)
out = sys.argv[1]
with open(out, 'w') as handle:
    handle.write(f'p cnf {nv} {len(clauses)}\n')
    handle.write(''.join(' '.join(map(str, cl)) + ' 0\n' for cl in clauses))
print(nv, len(clauses))
