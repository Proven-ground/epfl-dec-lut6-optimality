#!/usr/bin/env python3
"""Decoder synthesis by shared isolating signals (6-input LUTs).

When every primary output of the golden circuit is a distinct minterm of its n inputs (a decoder), the inputs are
split into r raw variables R and s = n - r selector variables S. Each of the 2^s selector points gets a distinct
label: a t-subset of k shared signals, t = 6 - r. Shared signal Y_i is one LUT over S, true exactly at the points
whose label contains i. The output for point q is one LUT over R and the t signals of its label:
[R = q_R] AND Y_label(q). Because all labels have size t and are distinct, the AND of a label's signals is true at
exactly one selector point, so every output is its minterm. LUTs = outputs + k, where k is the least integer with
C(k, t) >= 2^s, minimised over r. Levels = 2.

    onehot.py GOLDEN.aig OUT.blif      exit 0 and OUT written when GOLDEN is a decoder; exit 3 when it is not
"""
from __future__ import annotations

import itertools
import sys
from math import comb

K = 6


def parse_aiger(data: bytes):
    """Inputs, outputs (names from the symbol table, else ABC's default names) and AND gates of a combinational AIG."""
    newline = data.index(b'\n')
    kind, m, i, l, o, a = data[:newline].split()[:6]
    m, i, l, o, a = int(m), int(i), int(l), int(o), int(a)
    if l:
        raise ValueError('latches present')
    pos = newline + 1
    binary = kind == b'aig'
    if not binary:
        lines = data.decode().splitlines()[1:]
        inputs = [int(x) for x in lines[:i]]
        outs = [int(x) for x in lines[i:i + o]]
        ands = [tuple(map(int, x.split())) for x in lines[i + o:i + o + a]]
        rest = lines[i + o + a:]
    else:
        inputs = [2 * (k + 1) for k in range(i)]
        outs = []
        for _ in range(o):
            end = data.index(b'\n', pos)
            outs.append(int(data[pos:end]))
            pos = end + 1
        ands = []
        for k in range(a):
            lhs = 2 * (i + k + 1)
            deltas = []
            for _ in range(2):
                value, shift = 0, 0
                while True:
                    byte = data[pos]
                    pos += 1
                    value |= (byte & 0x7f) << shift
                    shift += 7
                    if not byte & 0x80:
                        break
                deltas.append(value)
            rhs0 = lhs - deltas[0]
            ands.append((lhs, rhs0, rhs0 - deltas[1]))
        rest = data[pos:].decode(errors='replace').splitlines()
    names_in = [f'pi{str(k).zfill(len(str(i - 1)) if i > 1 else 1)}' for k in range(i)]
    names_out = [f'po{str(k).zfill(len(str(o - 1)) if o > 1 else 1)}' for k in range(o)]
    for line in rest:
        if line.startswith('c'):
            break
        if line[:1] in ('i', 'o') and ' ' in line:
            index, name = line[1:].split(' ', 1)
            (names_in if line[0] == 'i' else names_out)[int(index)] = name
    return names_in, inputs, names_out, outs, ands


def truth_tables(data: bytes, max_inputs: int = 16):
    """Names and every output's truth table over all 2^n patterns; None when n > max_inputs."""
    names_in, inputs, names_out, outs, ands = parse_aiger(data)
    n = len(names_in)
    if n > max_inputs:
        return None
    width = 1 << n
    mask = (1 << width) - 1
    value = {0: 0}
    for k, lit in enumerate(inputs):
        word = 0
        for start in range(1 << k, width, 1 << (k + 1)):
            word |= ((1 << (1 << k)) - 1) << start
        value[lit >> 1] = word
    for lhs, r0, r1 in ands:
        value[lhs >> 1] = (value[r0 >> 1] ^ (mask if r0 & 1 else 0)) & (value[r1 >> 1] ^ (mask if r1 & 1 else 0))
    tts = [value[lit >> 1] ^ (mask if lit & 1 else 0) for lit in outs]
    return names_in, names_out, tts


def plan(n: int) -> tuple[int, int, int]:
    """(raw count r, label size t, shared signals k) with the fewest shared signals; ties keep the larger r."""
    best = None
    for r in range(max(0, n - K), min(K, n) + 1):
        t, points = K - r, 1 << (n - r)
        if t == 0:
            if points == 1:
                cand = (0, r, t)
            else:
                continue
        else:
            k = t
            while comb(k, t) < points:
                k += 1
            cand = (k, r, t)
        if best is None or cand[0] < best[0] or (cand[0] == best[0] and cand[1] > best[1]):
            best = cand
    k, r, t = best
    return r, t, k


def build(names_in: list[str], names_out: list[str], minterms: list[int]) -> str:
    n = len(names_in)
    r, t, k = plan(n)
    raw, sel = list(range(r)), list(range(r, n))
    labels = list(itertools.combinations(range(k), t))[:1 << len(sel)]
    shared = [f'{names_out[0]}__y{i}'.replace('[', '_').replace(']', '_') for i in range(k)]
    taken = set(names_in) | set(names_out)
    for i, name in enumerate(shared):
        while name in taken:
            name += '_'
        shared[i] = name
        taken.add(name)
    lines = ['.model top', '.inputs ' + ' '.join(names_in), '.outputs ' + ' '.join(names_out)]
    for i in range(k):  # Y_i over the selector variables: true where the point's label contains i
        lines.append('.names ' + ' '.join(names_in[v] for v in sel) + ' ' + shared[i])
        for point, label in enumerate(labels):
            if i in label:
                lines.append(''.join(str((point >> j) & 1) for j in range(len(sel))) + ' 1')
    for name, q in zip(names_out, minterms):
        q_raw = ''.join(str((q >> v) & 1) for v in raw)
        q_sel = sum(((q >> v) & 1) << j for j, v in enumerate(sel))
        label = labels[q_sel]
        lines.append('.names ' + ' '.join([names_in[v] for v in raw] + [shared[i] for i in label]) + ' ' + name)
        lines.append(q_raw + '1' * t + ' 1')
    lines.append('.end')
    return '\n'.join(lines) + '\n'


def main() -> int:
    tables = truth_tables(open(sys.argv[1], 'rb').read())
    if tables is None:
        return 3
    names_in, names_out, tts = tables
    n = len(names_in)
    minterms = []
    for tt in tts:
        if tt == 0 or tt & (tt - 1):
            return 3
        minterms.append(tt.bit_length() - 1)
    if len(set(minterms)) != len(minterms):
        return 3
    open(sys.argv[2], 'w').write(build(names_in, names_out, minterms))
    return 0


if __name__ == '__main__':
    sys.exit(main())
