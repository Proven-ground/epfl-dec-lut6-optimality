"""bound.py with the free-input base as a parameter, for the proof's control.

    python bound_base.py OUT.cnf BASE

BASE = 3 writes exactly bound.py's instance (same clause multiset): the 8-input decoder with one shared LUT,
UNSATISFIABLE. BASE = 2 writes the same encoding for the 7-input decoder (each output leaves 2 + u free inputs),
which is SATISFIABLE: the encoding admits solutions where they exist.
"""
import itertools
import sys

N = 6
BASE = int(sys.argv[2])
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
    for u in range(N - BASE + 1):
        for F in itertools.combinations(range(N), BASE + u):
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
