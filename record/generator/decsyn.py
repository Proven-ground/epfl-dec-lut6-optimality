#!/usr/bin/env python3
"""Decoder synthesis by isolating shared LUTs (6-input LUTs, two levels).

Applies when the golden circuit's outputs are all 2^n minterms of its n <= 16 inputs (a decoder); otherwise exits 3.
The network has k shared LUTs Y_1..Y_k, each reading up to 6 inputs, and one LUT per output: LUTs = 2^n + k, levels 2.
The output LUT for point q reads 6 signals A (inputs or shared LUTs) and is true exactly on q's code under A; it is
q's minterm exactly when that code is unique among all 2^n points (A isolates q). So the question is: do k shared
LUT functions exist under which every point is isolated by some 6 signals?

k ascends from the least feasible value (n <= 6: none; n = 7: one; n >= 8: two, because one shared LUT cannot serve
an 8-input decoder even with outputs feeding outputs, proven exhaustively by bound.py, and every larger decoder
contains that case). For k <= 2 the question is decided exactly: it is written as CNF over the shared LUTs' truth
tables, once per support class (permuting inputs maps a decoder to itself, so the supports matter only through how
many inputs they share), and solved by CaDiCaL; a model is the network. For k >= 3, simulated annealing over the
shared LUTs' truth tables and supports searches for a cover (seed and iteration count fixed). Below the closed-form
bound of onehot.py, its label construction is the answer. Every step is deterministic, and the netlist is checked
against every minterm before it is written.

    decsyn.py GOLDEN.aig OUT.blif [--seed S] [--iterations N]   exit 0 written, exit 3 not a decoder
"""
from __future__ import annotations

import argparse
import itertools
import json
import math
import os
import shutil
import subprocess
import sys
import tempfile
import time

from onehot import build, plan, truth_tables

K = 6
CADICAL = shutil.which('cadical') or '/root/chipforge/tools/cadical/c6073042/bin/cadical'


def proj(x: int, support: list[int]) -> int:
    return sum(((x >> v) & 1) << j for j, v in enumerate(support))


def isolation_cnf(n: int, supports: list[list[int]]) -> tuple[int, list[list[int]]]:
    """CNF whose models are truth tables (variables 64 i + 1 .. 64 i + 64 for shared LUT i) under which every point
    is isolated by 6 signals: both shared LUTs and 4 inputs, or one shared LUT and 5 inputs (k <= 2)."""
    count = 0

    def new() -> int:
        nonlocal count
        count += 1
        return count

    tables = [[new() for _ in range(64)] for _ in supports]
    value = [[tables[i][proj(x, s)] for x in range(1 << n)] for i, s in enumerate(supports)]
    clauses = [[-t[0]] for t in tables]  # a complemented shared LUT isolates the same points
    differ: dict[tuple[int, int], int] = {}

    def differs(a: int, b: int) -> int | None:
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
    groups = ([(list(range(k)), K - k)] if k > 1 else []) + [([i], K - 1) for i in range(k)]
    for q in range(1 << n):
        options = []
        for shared, raw in groups:
            for kept in itertools.combinations(range(n), raw):
                free = [v for v in range(n) if v not in kept]
                z = new()
                ok = True
                for bits in range(1, 1 << len(free)):
                    x = q
                    for j, v in enumerate(free):
                        if (bits >> j) & 1:
                            x ^= 1 << v
                    lits = [d for d in (differs(value[i][x], value[i][q]) for i in shared) if d is not None]
                    if not lits:
                        ok = False
                        break
                    clauses.append([-z] + lits)
                if ok:
                    options.append(z)
        clauses.append(options)
    return count, clauses


def solve(count: int, clauses: list[list[int]]) -> dict[int, bool] | None:
    with tempfile.NamedTemporaryFile('w', suffix='.cnf', delete=False) as handle:
        handle.write(f'p cnf {count} {len(clauses)}\n')
        handle.write(''.join(' '.join(map(str, c)) + ' 0\n' for c in clauses))
        path = handle.name
    try:
        run = subprocess.run([CADICAL, '-q', path], capture_output=True, text=True)
    finally:
        os.unlink(path)
    if run.returncode == 20:
        return None
    if run.returncode != 10:
        raise RuntimeError(f'cadical exit {run.returncode}: {(run.stdout + run.stderr)[-300:]}')
    model = {}
    for line in run.stdout.splitlines():
        if line.startswith('v'):
            for lit in map(int, line.split()[1:]):
                if lit:
                    model[abs(lit)] = lit > 0
    return model


def exact(n: int, k: int):
    """Shared LUTs (supports, truth tables) isolating every point, or None: decided by SAT for k <= 2."""
    first = list(range(min(K, n)))
    if k == 1:
        classes = [[first]]
    else:
        classes = [[first, list(range(K - o, 2 * K - o))] for o in range(max(0, 2 * K - n), K + 1)]
    for supports in classes:  # the overlap of the two supports is the only freedom; widest union first
        started = time.monotonic()
        model = solve(*isolation_cnf(n, supports))
        print(json.dumps({'k': k, 'supports': supports, 'satisfiable': model is not None,
                          'seconds': round(time.monotonic() - started, 1)}), flush=True)
        if model is not None:
            return supports, [sum(1 << m for m in range(64) if model.get(64 * i + m + 1)) for i in range(k)]
    return None


def anneal(n: int, k: int, seed: int, iterations: int):
    """Simulated annealing on k shared LUTs over the inputs for an isolation cover; None when none is reached."""
    import numpy as np
    rng = np.random.default_rng(seed)
    P = 1 << n
    points = np.arange(P)
    pis = np.array([(points >> v) & 1 for v in range(n)], dtype=np.uint8)
    subsets = np.array(list(itertools.combinations(range(n + k), K)), dtype=np.int64)
    subsets = subsets[(subsets >= n).any(axis=1)]
    by_signal = [np.nonzero((subsets == s).any(axis=1))[0] for s in range(n + k)]
    weights = (1 << np.arange(K)).astype(np.int64)

    def values(support, tt):
        idx = np.zeros(P, dtype=np.uint64)
        for j, v in enumerate(support):
            idx |= ((points >> v) & 1).astype(np.uint64) << np.uint64(j)
        return ((np.uint64(tt) >> idx) & np.uint64(1)).astype(np.uint8)

    def isolated(sig, rows):
        codes = (sig[subsets[rows]].astype(np.int64) * weights[None, :, None]).sum(axis=1)
        flat = codes + 64 * np.arange(len(rows))[:, None]
        counts = np.bincount(flat.ravel(), minlength=64 * len(rows))
        return (counts[flat] == 1).astype(np.int32)

    supports = [sorted(rng.choice(n, min(K, n), replace=False).tolist()) for _ in range(k)]
    tts = [int(rng.integers(0, 1 << 62)) | (int(rng.integers(0, 4)) << 62) for _ in range(k)]
    sig = np.concatenate([pis, np.array([values(s, t) for s, t in zip(supports, tts)], dtype=np.uint8)])
    iso = isolated(sig, np.arange(len(subsets)))
    cover = iso.sum(axis=0)
    score = int((cover > 0).sum())
    for step in range(iterations):
        if score == P:
            return supports, tts
        i = int(rng.integers(k))
        old_s, old_t = supports[i], tts[i]
        if rng.random() < 0.05:
            s = list(old_s)
            s[int(rng.integers(len(s)))] = int(rng.choice([v for v in range(n) if v not in s]))
            supports[i] = sorted(s)
        else:
            tts[i] = old_t ^ (1 << int(rng.integers(64)))
        rows = by_signal[n + i]
        sig[n + i] = values(supports[i], tts[i])
        new_rows = isolated(sig, rows)
        new_cover = cover - iso[rows].sum(axis=0) + new_rows.sum(axis=0)
        new_score = int((new_cover > 0).sum())
        temperature = max(0.05, 2.0 * (1 - step / iterations))
        if new_score >= score or rng.random() < math.exp((new_score - score) / temperature):
            cover, score = new_cover, new_score
            iso[rows] = new_rows
        else:
            supports[i], tts[i] = old_s, old_t
            sig[n + i] = values(old_s, old_t)
    return (supports, tts) if score == P else None


def network(names_in: list[str], names_out: list[str], minterms: list[int], supports, tts) -> str:
    """Two-level netlist: the shared LUTs, then each output over the first 6 signals (lexicographic) isolating it.
    Raises when a point is not isolated or an output is not its minterm."""
    n, k = len(names_in), len(supports)
    taken = set(names_in) | set(names_out)
    shared = []
    for j in range(k):
        name = f'dec_y{j}'
        while name in taken:
            name += '_'
        taken.add(name)
        shared.append(name)
    signal = [[(x >> v) & 1 for x in range(1 << n)] for v in range(n)]
    signal += [[(tt >> proj(x, s)) & 1 for x in range(1 << n)] for s, tt in zip(supports, tts)]
    names = list(names_in) + shared
    codes = {}
    for subset in itertools.combinations(range(n + k), K):
        column = [sum(signal[s][x] << j for j, s in enumerate(subset)) for x in range(1 << n)]
        counts: dict[int, int] = {}
        for c in column:
            counts[c] = counts.get(c, 0) + 1
        codes[subset] = (column, counts)
    lines = ['.model top', '.inputs ' + ' '.join(names_in), '.outputs ' + ' '.join(names_out)]
    for name, support, tt in zip(shared, supports, tts):
        lines.append('.names ' + ' '.join(names_in[v] for v in support) + ' ' + name)
        lines += [''.join(str((m >> b) & 1) for b in range(len(support))) + ' 1'
                  for m in range(1 << len(support)) if (tt >> m) & 1]
    for name, q in zip(names_out, minterms):
        subset = next((s for s, (column, counts) in codes.items() if counts[column[q]] == 1), None)
        if subset is None:
            raise RuntimeError(f'point {q} is not isolated')
        column = codes[subset][0]
        if [x for x in range(1 << n) if column[x] == column[q]] != [q]:
            raise RuntimeError(f'output {name} is not the minterm of {q}')
        lines.append('.names ' + ' '.join(names[s] for s in subset) + ' ' + name)
        lines.append(''.join(str(signal[s][q]) for s in subset) + ' 1')
    lines.append('.end')
    return '\n'.join(lines) + '\n'


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('golden')
    parser.add_argument('out')
    parser.add_argument('--seed', type=int, default=1)
    parser.add_argument('--iterations', type=int, default=60000)
    args = parser.parse_args()
    tables = truth_tables(open(args.golden, 'rb').read())
    if tables is None:
        return 3
    names_in, names_out, tts = tables
    n = len(names_in)
    minterms = []
    for tt in tts:
        if tt == 0 or tt & (tt - 1):
            return 3
        minterms.append(tt.bit_length() - 1)
    if len(set(minterms)) != len(minterms) or len(minterms) != 1 << n:
        return 3
    if n <= K:  # every output is one LUT over all inputs
        lines = ['.model top', '.inputs ' + ' '.join(names_in), '.outputs ' + ' '.join(names_out)]
        for name, q in zip(names_out, minterms):
            lines += ['.names ' + ' '.join(names_in) + ' ' + name, ''.join(str((q >> v) & 1) for v in range(n)) + ' 1']
        open(args.out, 'w').write('\n'.join(lines + ['.end']) + '\n')
        return 0
    _, _, k_label = plan(n)
    for k in range(1 if n == K + 1 else 2, k_label):
        found = exact(n, k) if k <= 2 else anneal(n, k, args.seed, args.iterations)
        if found:
            open(args.out, 'w').write(network(names_in, names_out, minterms, *found))
            return 0
    open(args.out, 'w').write(build(names_in, names_out, minterms))
    return 0


if __name__ == '__main__':
    sys.exit(main())
