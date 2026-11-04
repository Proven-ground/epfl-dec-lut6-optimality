#!/usr/bin/env python3
"""Exhaustive simulation of record/out.blif against the board's benchmark, with readers written for this check only.

Reads the benchmark AIGER (binary or ASCII) and the BLIF with its own parsers (no code shared with the generator),
evaluates both on all 2^n input patterns, every signal held as a 2^n-bit integer, and compares every output by name.
It also checks the netlist's structure: every node has exactly six inputs, none is a constant, a buffer or an
inverter, and the longest path is two nodes.

    python3 simulate_dec.py dec.aig [record/out.blif]      exit 0 when every output matches and the structure holds
"""
import sys


def read_aiger(path):
    data = open(path, 'rb').read()
    newline = data.index(b'\n')
    header = data[:newline].split()
    kind, M, I, L, O, A = header[0], *map(int, header[1:6])
    if L:
        raise ValueError('latches are not combinational')
    pos = newline + 1
    if kind == b'aag':
        lines = data.decode().split('\n')[1:]
        inputs = [int(x) for x in lines[:I]]
        outputs = [int(x) for x in lines[I:I + O]]
        ands = [tuple(map(int, x.split())) for x in lines[I + O:I + O + A]]
        tail = lines[I + O + A:]
    elif kind == b'aig':
        inputs = [2 * (k + 1) for k in range(I)]
        outputs = []
        for _ in range(O):
            end = data.index(b'\n', pos)
            outputs.append(int(data[pos:end]))
            pos = end + 1
        ands = []
        for k in range(A):
            lhs = 2 * (I + k + 1)
            deltas = []
            for _ in range(2):
                value, shift = 0, 0
                while True:
                    byte = data[pos]
                    pos += 1
                    value |= (byte & 0x7F) << shift
                    shift += 7
                    if byte < 0x80:
                        break
                deltas.append(value)
            ands.append((lhs, lhs - deltas[0], lhs - deltas[0] - deltas[1]))
        tail = data[pos:].decode(errors='replace').split('\n')
    else:
        raise ValueError(f'not an AIGER file: {kind!r}')
    in_names, out_names = [None] * I, [None] * O
    for line in tail:
        if line.startswith('c'):
            break
        if line[:1] in ('i', 'o') and ' ' in line:
            index, name = line[1:].split(' ', 1)
            (in_names if line[0] == 'i' else out_names)[int(index)] = name
    if None in in_names or None in out_names:
        raise ValueError('the AIGER symbol table does not name every input and output')
    return in_names, inputs, out_names, outputs, ands


def input_words(n):
    full = (1 << (1 << n)) - 1
    words = []
    for v in range(n):
        word = 0
        for x in range(1 << n):
            if (x >> v) & 1:
                word |= 1 << x
        words.append(word)
    return words, full


def eval_aiger(path):
    in_names, inputs, out_names, outputs, ands = read_aiger(path)
    words, full = input_words(len(in_names))
    value = {0: 0}
    for lit, word in zip(inputs, words):
        value[lit >> 1] = word
    for lhs, a, b in ands:
        va = value[a >> 1] ^ (full if a & 1 else 0)
        vb = value[b >> 1] ^ (full if b & 1 else 0)
        value[lhs >> 1] = va & vb
    result = {name: value[lit >> 1] ^ (full if lit & 1 else 0) for name, lit in zip(out_names, outputs)}
    return in_names, result


def eval_blif(path, in_names):
    words, full = input_words(len(in_names))
    value = dict(zip(in_names, words))
    level = {name: 0 for name in in_names}
    declared_in, declared_out, problems = [], [], []
    lines = [l.rstrip() for l in open(path)]
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith('.inputs'):
            declared_in = line.split()[1:]
        elif line.startswith('.outputs'):
            declared_out = line.split()[1:]
        elif line.startswith('.names'):
            sig = line.split()[1:]
            ins, out = sig[:-1], sig[-1]
            rows = []
            i += 1
            while i < len(lines) and lines[i] and not lines[i].startswith('.'):
                rows.append(lines[i].split())
                i += 1
            if len(ins) != 6:
                problems.append(f'{out} has {len(ins)} inputs')
            word = 0
            for row in rows:
                cube, bit = (row[0], row[1]) if ins else ('', row[0])
                if bit != '1':
                    problems.append(f'{out} has an off-set row')
                term = full
                for ch, s in zip(cube, ins):
                    if ch == '1':
                        term &= value[s]
                    elif ch == '0':
                        term &= ~value[s] & full
                word |= term
            if word in (0, full) or any(word in (value[s], value[s] ^ full) for s in ins):
                problems.append(f'{out} is a constant, buffer or inverter')
            value[out] = word
            level[out] = 1 + max((level[s] for s in ins), default=0)
            continue
        i += 1
    if declared_in != in_names:
        problems.append('the BLIF inputs differ from the benchmark inputs in name or order')
    return declared_out, value, level, problems


def main():
    aig = sys.argv[1]
    blif = sys.argv[2] if len(sys.argv) > 2 else 'record/out.blif'
    in_names, golden = eval_aiger(aig)
    declared_out, value, level, problems = eval_blif(blif, in_names)
    if declared_out != list(golden):
        problems.append('the BLIF outputs differ from the benchmark outputs in name or order')
    missing = [name for name in golden if name not in value]
    wrong = [name for name in golden if name in value and value[name] != golden[name]]
    depth = max((level[name] for name in golden if name in level), default=0)
    nodes = len([k for k in level if k not in in_names])
    print(f'{len(in_names)} inputs, {len(golden)} outputs, {nodes} nodes, depth {depth}; '
          f'outputs compared on all {1 << len(in_names)} patterns: {len(golden) - len(missing) - len(wrong)} match, '
          f'{len(wrong)} differ, {len(missing)} missing')
    for problem in problems[:10]:
        print('structure:', problem)
    ok = not wrong and not missing and not problems and depth == 2
    print('equivalent and well formed' if ok else 'FAIL')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
