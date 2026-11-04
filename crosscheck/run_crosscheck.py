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
UNSAT would be a network the reduction drops. Every SAT answer is decoded and simulated on every pattern.
Positive controls: (K, K) with 2^K nodes is satisfiable (one LUT per output), and the 3-input decoder has a
12-node network of 2-input LUTs.

Every comparison is judged by judge() or relate(). A decoded network that mismatches its minterms on any pattern,
or an answer contrary to the expected one, is a violation; a solver that times out or fails is incomplete. The run
ends with both counts and exits 1 on any violation, 2 when a comparison is incomplete and none is violated, 0 only
when every comparison was decided and held.

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

DECIDED = ('SAT', 'UNSAT')


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


def judge(answer, mismatches, expected):
    """'ok', 'violation' or 'incomplete' for one solver answer against the expected one.
    mismatches is the simulation count of the decoded network (None when there is no model)."""
    if answer not in DECIDED:
        return 'incomplete'
    if answer == 'SAT' and mismatches != 0:
        return 'violation'
    return 'ok' if answer == expected else 'violation'


def relate(direct, direct_mismatches, reduced):
    """Verdict and wording for the 2^n + 1 comparison: direct SAT must imply reduced SAT."""
    if direct not in DECIDED or reduced not in DECIDED:
        return 'incomplete', 'undecided within the time limit'
    if direct == 'SAT' and direct_mismatches != 0:
        return 'violation', 'VIOLATION: the decoded network is not a decoder'
    if direct == 'SAT' and reduced == 'UNSAT':
        return 'violation', 'VIOLATION: the reduction drops a legal network'
    if direct == 'SAT':
        return 'ok', 'consistent: network exists, reduction admits it'
    if reduced == 'UNSAT':
        return 'ok', 'consistent: both refute'
    return 'ok', 'consistent: reduction is only necessary'


def roles(cadical, work, K, n, extra, timeout):
    """Solve a role-fixed direct instance; (answer, seconds, mismatches or None)."""
    path = os.path.join(work, f'roles_{K}_{n}_{extra}.cnf')
    nv, nc, meta = direct_roles.build(path, K, n, extra)
    ans, model, sec = solve(cadical, path, timeout)
    mismatches = None
    if ans == 'SAT':
        nodes, order = direct_roles.decode(model, meta)
        mismatches = direct_roles.simulate(nodes, order, K, n)
    return ans, sec, mismatches


def shown(mismatches):
    return '' if mismatches is None else f' (network decoded, mismatches {mismatches})'


def main():
    cadical = sys.argv[1]
    timeout = float(sys.argv[sys.argv.index('--timeout') + 1]) if '--timeout' in sys.argv else 1800.0
    if '--cases' in sys.argv:
        cases = [tuple(map(int, c.split(','))) for c in sys.argv[sys.argv.index('--cases') + 1:]]
    else:
        cases = [(2, 3), (3, 4), (3, 5), (4, 5), (4, 6), (5, 6)]
    work = tempfile.mkdtemp(prefix='crosscheck_')
    tally = {'ok': 0, 'violation': 0, 'incomplete': 0}

    def record(verdict):
        tally[verdict] += 1
        return '' if verdict == 'ok' else f'  [{verdict.upper()}]'

    print('positive controls')
    for K in sorted({K for K, _ in cases}):
        ans, sec, mis = roles(cadical, work, K, K, 0, timeout)
        print(f'  K={K} n={K} nodes={1 << K}: {ans} {sec}s{shown(mis)}  expected SAT{record(judge(ans, mis, "SAT"))}')
    path = os.path.join(work, 'direct_2_3_12.cnf')
    nv, cl, meta = direct_bound.encode(2, 3, 12)
    direct_bound.write(path, nv, cl)
    ans, model, sec = solve(cadical, path, timeout)
    mis = None
    if ans == 'SAT':
        nodes, outputs = direct_bound.decode(model, meta)
        mis = direct_bound.simulate(nodes, outputs, 2, 3)
    print(f'  fully direct K=2 n=3 nodes=12: {ans} {sec}s{shown(mis)}  expected SAT{record(judge(ans, mis, "SAT"))}')
    for m in (8, 9):
        path = os.path.join(work, f'direct_2_3_{m}.cnf')
        nv, cl, meta = direct_bound.encode(2, 3, m)
        direct_bound.write(path, nv, cl)
        ans, model, sec = solve(cadical, path, timeout)
        mis = None
        if ans == 'SAT':
            nodes, outputs = direct_bound.decode(model, meta)
            mis = direct_bound.simulate(nodes, outputs, 2, 3)
        print(f'  fully direct K=2 n=3 nodes={m}: {ans} {sec}s{shown(mis)}  expected UNSAT, as the role-fixed '
              f'encoder below{record(judge(ans, mis, "UNSAT"))}')
    print(f'\n{"K":>2} {"n":>2} {"LUTs":>5} {"direct":>8} {"s":>8} {"reduced":>8} {"s":>8}  relation')
    for K, n in cases:
        P = 1 << n
        ans, sec, mis = roles(cadical, work, K, n, 0, timeout)
        print(f'{K:>2} {n:>2} {P:>5} {ans:>8} {sec:>8} {"":>8} {"":>8}  Lemma 2 analogue, expected UNSAT'
              f'{shown(mis)}{record(judge(ans, mis, "UNSAT"))}')
        d_ans, d_sec, d_mis = roles(cadical, work, K, n, 1, timeout)
        rpath = os.path.join(work, f'reduced_{K}_{n}.cnf')
        reduced_bound.write(rpath, K, n)
        r_ans, _, r_sec = solve(cadical, rpath, timeout)
        verdict, relation = relate(d_ans, d_mis, r_ans)
        print(f'{K:>2} {n:>2} {P + 1:>5} {d_ans:>8} {d_sec:>8} {r_ans:>8} {r_sec:>8}  {relation}{shown(d_mis)}'
              f'{record(verdict)}')
    print(f'\ncomparisons: {sum(tally.values())}  held: {tally["ok"]}  violations: {tally["violation"]}  '
          f'incomplete: {tally["incomplete"]}')
    if tally['violation']:
        return 1
    return 2 if tally['incomplete'] else 0


if __name__ == '__main__':
    sys.exit(main())
