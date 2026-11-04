#!/usr/bin/env python3
"""Enumerate which of the two shared LUTs of record/out.blif can isolate each of the 256 input patterns.

Reads the two shared LUTs (supports and truth tables) from the netlist itself. A pattern q is isolated by a shared
LUT Y together with five raw inputs when some choice of five inputs leaves three free inputs such that every
pattern x != q agreeing with q on the five inputs has Y(x) != Y(q). Prints, for each shared LUT, how many patterns
it isolates, how many patterns both or neither isolate, and checks the rule stated in the paper: Y0 isolates
exactly the patterns with count[2] = count[4] and Y1 exactly the others.

    python3 partition.py [record/out.blif]      exit 0 when the rule holds, exit 1 otherwise
"""
import itertools
import sys

N = 8


def read_shared(path):
    names_in, shared, block = [], [], None
    for line in open(path):
        if line.startswith('.inputs'):
            names_in = line.split()[1:]
        elif line.startswith('.names'):
            sig = line.split()[1:]
            block = None
            if sig[-1].startswith('dec_y'):
                block = (sig[-1], [names_in.index(s) for s in sig[:-1]], [])
                shared.append(block)
        elif block is not None and line.strip() and not line.startswith('.'):
            block[2].append(line.split()[0])
    tables = []
    for name, support, rows in shared:
        tt = 0
        for row in rows:
            tt |= 1 << sum(int(ch) << j for j, ch in enumerate(row))
        tables.append((name, support, tt))
    return tables


def value(tt, support, x):
    return (tt >> sum(((x >> v) & 1) << j for j, v in enumerate(support))) & 1


def isolates(tt, support, q):
    for kept in itertools.combinations(range(N), 5):
        free = [v for v in range(N) if v not in kept]
        if all(value(tt, support, q ^ sum(1 << v for j, v in enumerate(free) if (bits >> j) & 1)) != value(tt, support, q)
               for bits in range(1, 8)):
            return True
    return False


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else 'record/out.blif'
    tables = read_shared(path)
    sets = []
    for name, support, tt in tables:
        iso = {q for q in range(1 << N) if isolates(tt, support, q)}
        sets.append(iso)
        print(f'{name} support {support} table 0x{tt:016x} isolates {len(iso)} patterns')
    both = sets[0] & sets[1]
    neither = set(range(1 << N)) - (sets[0] | sets[1])
    print(f'both {len(both)}  neither {len(neither)}')
    rule = {q for q in range(1 << N) if ((q >> 2) & 1) == ((q >> 4) & 1)}
    ok = sets[0] == rule and sets[1] == set(range(1 << N)) - rule
    print('rule count[2] = count[4] for Y0 and its complement for Y1:', 'holds' if ok else 'FAILS')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main())
