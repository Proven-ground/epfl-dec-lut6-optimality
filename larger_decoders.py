#!/usr/bin/env python3
"""Two-level LUT-6 networks for the n-input decoder, n = 9 .. 12, built and checked exhaustively.

The label construction (record/generator/onehot.py, used for n <= 11): r raw inputs and s = n - r selector inputs,
each selector point labelled by a distinct t-subset (t = 6 - r) of k shared LUTs over the selectors; the output for
q is the conjunction of its raw literals and its label's shared LUTs. The block construction (n <= 36): the inputs
are split into at most six blocks of at most six inputs; every block of two or more inputs is decoded into its
minterms, one shared LUT each; the output for q is the conjunction of the single-input blocks' literals and, per
larger block, the shared LUT of q's pattern on that block.

For each n the script builds the cheaper of the two as a BLIF-style netlist, checks that every node has at most six
inputs and that the network has two levels, and simulates it on all 2^n input patterns, every signal held as a
2^n-bit integer, comparing every output with its minterm.

    python3 larger_decoders.py        prints one line per n; exit 0 when all four networks are correct
"""
import itertools
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'record', 'generator'))
from onehot import build, plan  # noqa: E402

K = 6


def block_netlist(n):
    """The cheapest block partition: as many single-input blocks as allowed, the rest in blocks of at most six."""
    best = None

    def parts(rem, maxp, cnt):
        if rem == 0:
            yield ()
            return
        if cnt == K:
            return
        for p in range(min(rem, maxp), 0, -1):
            for rest in parts(rem - p, p, cnt + 1):
                yield (p,) + rest
    for ps in parts(n, K, 0):
        cost = sum(1 << b for b in ps if b >= 2)
        if best is None or cost < best[0]:
            best = (cost, ps)
    _, sizes = best
    names_in = [f'x{v}' for v in range(n)]
    lines = ['.model top', '.inputs ' + ' '.join(names_in), '.outputs ' + ' '.join(f'o{q}' for q in range(1 << n))]
    blocks, start = [], 0
    for b in sizes:
        blocks.append(list(range(start, start + b)))
        start += b
    for i, blk in enumerate(blocks):
        if len(blk) < 2:
            continue
        for pat in range(1 << len(blk)):
            lines.append('.names ' + ' '.join(names_in[v] for v in blk) + f' b{i}_{pat}')
            lines.append(''.join(str((pat >> j) & 1) for j in range(len(blk))) + ' 1')
    for q in range(1 << n):
        sig, bits = [], []
        for i, blk in enumerate(blocks):
            if len(blk) == 1:
                sig.append(names_in[blk[0]])
                bits.append(str((q >> blk[0]) & 1))
            else:
                pat = sum(((q >> v) & 1) << j for j, v in enumerate(blk))
                sig.append(f'b{i}_{pat}')
                bits.append('1')
        lines.append('.names ' + ' '.join(sig) + f' o{q}')
        lines.append(''.join(bits) + ' 1')
    lines.append('.end')
    return '\n'.join(lines) + '\n', sizes


def check(blif, n):
    """Bit-parallel exhaustive simulation. Returns (LUTs, levels, max fanin, mismatching outputs)."""
    P = 1 << n
    full = (1 << P) - 1
    val, level = {}, {}
    for v in range(n):
        word = 0
        for x in range(P):
            if (x >> v) & 1:
                word |= 1 << x
        val[f'x{v}'] = word
        level[f'x{v}'] = 0
    luts, max_fanin = 0, 0
    lines = blif.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith('.names'):
            sig = line.split()[1:]
            ins, out = sig[:-1], sig[-1]
            rows = []
            i += 1
            while i < len(lines) and not lines[i].startswith('.'):
                rows.append(lines[i].split()[0])
                i += 1
            word = 0
            for row in rows:
                term = full
                for ch, s in zip(row, ins):
                    if ch == '1':
                        term &= val[s]
                    elif ch == '0':
                        term &= ~val[s] & full
                word |= term
            val[out] = word
            level[out] = 1 + max(level[s] for s in ins)
            luts += 1
            max_fanin = max(max_fanin, len(ins))
        else:
            i += 1
    bad = sum(1 for q in range(P) if val[f'o{q}'] != 1 << q)
    return luts, max(level[f'o{q}'] for q in range(P)), max_fanin, bad


def accept(blif, n, shared):
    """(verdict, measurements) for one network: it must be correct on every pattern, have exactly 2^n + shared LUTs,
    two levels, and fan-in at most six. Any other outcome, including an unreadable netlist, is a failure."""
    try:
        luts, levels, fanin, bad = check(blif, n)
    except (KeyError, ValueError, IndexError) as error:
        return False, f'netlist does not evaluate: {error!r}'
    good = bad == 0 and luts == (1 << n) + shared and levels == 2 and fanin <= K
    return good, f'LUTs {luts:5d}, levels {levels}, max fanin {fanin}, mismatching outputs {bad}'


def main():
    ok = True
    for n in (9, 10, 11, 12):
        candidates = []
        try:
            r, t, k = plan(n)
            if t >= 1:
                blif = build([f'x{v}' for v in range(n)], [f'o{q}' for q in range(1 << n)], list(range(1 << n)))
                candidates.append(('label', k, blif, f'r={r} t={t} k={k}'))
        except TypeError:
            pass
        blif, sizes = block_netlist(n)
        candidates.append(('block', sum(1 << b for b in sizes if b >= 2), blif, f'blocks {sizes}'))
        kind, shared, blif, detail = min(candidates, key=lambda c: c[1])
        good, measured = accept(blif, n, shared)
        ok &= good
        print(f'n={n:2d} {kind:5s} ({detail}): shared {shared:3d}, {measured}  {"ok" if good else "FAIL"}', flush=True)
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
