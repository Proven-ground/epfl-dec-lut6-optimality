#!/usr/bin/env python3
"""Cross-check the paper's reduction against direct circuit encodings on small LUT sizes.

Three encoders take part:
  reduced_bound.py  the paper's reduction (Lemmas 1 to 3) parametrised by K and n; with K = 6 it writes the stored
                    8-input instance and 7-input control clause for clause.
  direct_roles.py   a direct circuit encoding that uses only Lemma 1 (each output is its own node); free fanins,
                    free tables, free build order; this is what tests Lemmas 2 and 3 and the encoder.
  direct_bound.py   a fully direct encoding with free node roles, feasible only for the tiniest case; it must agree
                    with direct_roles.py there.

For each (K, n) with K < n <= 2K - 1 the driver asks whether 2^n LUTs suffice (Lemma 2 says never) and whether
2^n + 1 LUTs suffice (the question the paper's reduction answers for K = 6, n = 8). The reduction is a necessary
condition, so the relation that must hold is: direct SAT implies reduced SAT. A case with direct SAT and reduced
UNSAT would be a network the reduction drops. Every SAT answer is decoded, simulated on every pattern and checked.
Positive controls: (K, K) with 2^K nodes is satisfiable (one LUT per output), and the 3-input decoder has a
12-node network of 2-input LUTs.

    python3 run_crosscheck.py CADICAL [--timeout SECONDS] [--cases K,n ...]
"""
import os
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import direct_bound
import direct_roles
import reduced_bound


def solve(cadical, path, timeout):
    started = time.monotonic()
    try:
        run = subprocess.run([cadical, '-q', path], capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return 'TIMEOUT', None, round(time.monotonic() - started, 1)
    seconds = round(time.monotonic() - started, 1)
    if run.returncode == 20:
        return 'UNSAT', None, seconds
    if run.returncode == 10:
        model = {}
        for line in run.stdout.splitlines():
            if line.startswith('v'):
                for lit in map(int, line.split()[1:]):
                    if lit:
                        model[abs(lit)] = lit > 0
        return 'SAT', model, seconds
    return f'EXIT{run.returncode}', None, seconds


def roles(cadical, work, K, n, extra, timeout):
    path = os.path.join(work, f'roles_{K}_{n}_{extra}.cnf')
    nv, nc, meta = direct_roles.build(path, K, n, extra)
    ans, model, sec = solve(cadical, path, timeout)
    note = ''
    if ans == 'SAT':
        nodes, order = direct_roles.decode(model, meta)
        note = f' (network decoded, mismatches {direct_roles.simulate(nodes, order, K, n)})'
    return ans, sec, note


def main():
    cadical = sys.argv[1]
    timeout = float(sys.argv[sys.argv.index('--timeout') + 1]) if '--timeout' in sys.argv else 1800.0
    if '--cases' in sys.argv:
        cases = [tuple(map(int, c.split(','))) for c in sys.argv[sys.argv.index('--cases') + 1:]]
    else:
        cases = [(2, 3), (3, 4), (3, 5), (4, 5), (4, 6), (5, 6)]
    work = tempfile.mkdtemp(prefix='crosscheck_')
    violations = 0
    print('positive controls')
    for K in sorted({K for K, _ in cases}):
        ans, sec, note = roles(cadical, work, K, K, 0, timeout)
        print(f'  K={K} n={K} nodes={1 << K}: {ans} {sec}s{note}  expected SAT')
        violations += ans != 'SAT'
    path = os.path.join(work, 'direct_2_3_12.cnf')
    nv, cl, meta = direct_bound.encode(2, 3, 12)
    direct_bound.write(path, nv, cl)
    ans, model, sec = solve(cadical, path, timeout)
    note = ''
    if ans == 'SAT':
        nodes, outputs = direct_bound.decode(model, meta)
        note = f' (network decoded, mismatches {direct_bound.simulate(nodes, outputs, 2, 3)})'
    print(f'  fully direct K=2 n=3 nodes=12: {ans} {sec}s{note}  expected SAT')
    violations += ans != 'SAT'
    for m in (8, 9):
        path = os.path.join(work, f'direct_2_3_{m}.cnf')
        nv, cl, meta = direct_bound.encode(2, 3, m)
        direct_bound.write(path, nv, cl)
        ans, model, sec = solve(cadical, path, timeout)
        print(f'  fully direct K=2 n=3 nodes={m}: {ans} {sec}s  must agree with the role-fixed encoder below')
    print(f'\n{"K":>2} {"n":>2} {"LUTs":>5} {"direct":>8} {"s":>8} {"reduced":>8} {"s":>8}  relation')
    for K, n in cases:
        P = 1 << n
        ans, sec, note = roles(cadical, work, K, n, 0, timeout)
        print(f'{K:>2} {n:>2} {P:>5} {ans:>8} {sec:>8} {"":>8} {"":>8}  Lemma 2 analogue, expected UNSAT{note}')
        violations += ans == 'SAT'
        d_ans, d_sec, note = roles(cadical, work, K, n, 1, timeout)
        rpath = os.path.join(work, f'reduced_{K}_{n}.cnf')
        reduced_bound.write(rpath, K, n)
        r_ans, _, r_sec = solve(cadical, rpath, timeout)
        if d_ans == 'SAT' and r_ans == 'UNSAT':
            relation = 'VIOLATION: the reduction drops a legal network'
            violations += 1
        elif d_ans == 'SAT' and r_ans == 'SAT':
            relation = 'consistent: network exists, reduction admits it'
        elif d_ans == 'UNSAT' and r_ans == 'UNSAT':
            relation = 'consistent: both refute'
        elif d_ans == 'UNSAT' and r_ans == 'SAT':
            relation = 'consistent: reduction is only necessary'
        else:
            relation = 'undecided within the time limit'
        print(f'{K:>2} {n:>2} {P + 1:>5} {d_ans:>8} {d_sec:>8} {r_ans:>8} {r_sec:>8}  {relation}{note}')
    print('\nviolations:', violations)
    return 1 if violations else 0


if __name__ == '__main__':
    sys.exit(main())
