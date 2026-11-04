#!/usr/bin/env python3
"""Plant the paper's 7-input construction into the direct encoding at the paper's LUT size and solve it.

The 7-input decoder in 129 six-input LUTs: one shared LUT Y over inputs 0 to 5 with table 0x000ff0ffff0ff000, and
each output reading Y and five inputs (decsyn.py's network(), first isolating 6-subset per point). The script builds
that network, checks it by exhaustive simulation, plants it into direct_roles.py's encoding with K = 6, n = 7 and
one extra node, and solves: the encoding must admit it. The decoded model is simulated again.

    python3 plant_witness.py CADICAL WORKDIR
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..', 'record', 'generator'))
import direct_roles  # noqa: E402
import run_crosscheck  # noqa: E402
from decsyn import network  # noqa: E402

K, n = 6, 7
Y_SUPPORT, Y_TABLE = [0, 1, 2, 3, 4, 5], 0x000ff0ffff0ff000


def witness_nodes():
    names_in = [f'x{v}' for v in range(n)]
    names_out = [f'o{q}' for q in range(1 << n)]
    blif = network(names_in, names_out, list(range(1 << n)), [Y_SUPPORT], [Y_TABLE])
    signal = {name: v for v, name in enumerate(names_in)}
    signal.update({f'o{q}': n + 1 + q for q in range(1 << n)})
    nodes = [None] * ((1 << n) + 1)
    lines = blif.splitlines()
    i = 0
    while i < len(lines):
        if lines[i].startswith('.names'):
            sig = lines[i].split()[1:]
            rows = []
            i += 1
            while i < len(lines) and not lines[i].startswith('.'):
                rows.append(lines[i].split()[0])
                i += 1
            ins, out = sig[:-1], sig[-1]
            j = (1 << n) if out.startswith('dec_y') else int(out[1:])
            fanin = [n + 1 + (1 << n) if s.startswith('dec_y') else signal[s] for s in ins]
            table = 0
            for row in rows:
                table |= 1 << sum(int(ch) << p for p, ch in enumerate(row))
            while len(fanin) < K:  # pad unused pins with the constant; the table ignores them
                fanin.append(n)
                table |= table << (1 << (len(fanin) - 1))
            nodes[j] = (fanin, table)
        else:
            i += 1
    return nodes


def main():
    cadical, work = sys.argv[1], sys.argv[2]
    nodes = witness_nodes()
    pre = direct_roles.simulate(nodes, None, K, n)
    print(f'witness network: {len(nodes)} nodes, simulation mismatches {pre}', flush=True)
    path = os.path.join(work, 'planted_witness_6_7.cnf')
    nv, nc, meta = direct_roles.build(path, K, n, 1, plant=nodes)
    print(f'planted instance: {nv} variables, {nc} clauses', flush=True)
    answer, model, seconds = run_crosscheck.solve(cadical, path, 3600)
    post = None
    if answer == 'SAT':
        decoded, _ = direct_roles.decode(model, meta)
        post = direct_roles.simulate(decoded, None, K, n)
    print(f'solver: {answer} in {seconds} s; decoded network mismatches {post}')
    held = pre == 0 and answer == 'SAT' and post == 0
    print('the direct encoding admits the paper\'s 7-input construction:', 'yes' if held else 'NO')
    return 0 if held else 1


if __name__ == '__main__':
    sys.exit(main())
