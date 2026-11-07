"""Prefix isolation with lossless first-helper NPN and pin symmetries.

NPN representatives are enumerated exhaustively for K<=4 on Modal. A global
primary-input permutation/complement and helper-output complement give a
representative without changing the decoder problem. Later helper pins are
distinct and sorted: unused pins are padded with distinct primary inputs.
"""
import functools
import itertools
import json

import isolation_bound as base
from direct_multi import HEADER_WIDTH, read_model, simulate, topological

decode = base.decode


@functools.lru_cache(None)
def representatives(K):
    if K not in (2, 3, 4):
        raise ValueError('exhaustive NPN normalization is limited to K=2,3,4')
    rows = 1 << K
    full = (1 << rows) - 1
    permutations = list(itertools.permutations(range(K)))
    maps = []
    for permutation in permutations:
        mapping = [sum(((x >> i) & 1) << permutation[i] for i in range(K))
                   for x in range(rows)]
        maps.extend(tuple(mapping[x] ^ shift for x in range(rows)) for shift in range(rows))
    covered = set()
    reps = []
    sizes = []
    for table in range(0, full + 1, 2):
        if table in covered:
            continue
        orbit = set()
        for mapping in maps:
            transformed = sum(((table >> source) & 1) << x for x, source in enumerate(mapping))
            orbit.add(transformed ^ (full if transformed & 1 else 0))
        if covered.intersection(orbit):
            raise AssertionError('NPN classes overlap')
        if min(orbit) != table:
            raise AssertionError('representative is not minimal')
        covered.update(orbit)
        reps.append(table)
        sizes.append(len(orbit))
    if len(covered) != 1 << (rows - 1):
        raise AssertionError('truth-table coverage is incomplete')
    return tuple(reps), tuple(sizes)


def build(path, K, n, extra, plant=None):
    nv, nc, meta = base.build(path, K, n, extra, plant)
    additions = []

    def new():
        nonlocal nv
        nv += 1
        return nv

    def clause(literals):
        additions.append(list(literals))

    reps, sizes = representatives(K)
    choices = []
    for table in reps:
        option = new()
        choices.append(option)
        for row, variable in enumerate(meta['tables'][0]):
            clause([-option, variable if (table >> row) & 1 else -variable])
    clause(choices)
    for pins in meta['selectors'][1:]:
        for selected in pins:
            clause([-selected[n]])
        signals = sorted(signal for signal in pins[0] if signal != n)
        for previous, following in zip(pins, pins[1:]):
            for i, signal in enumerate(signals):
                clause([-previous[signal]] + [following[s] for s in signals[i + 1:]])
    with open(path, 'r+', newline='\n') as output:
        output.seek(0, 2)
        for literals in additions:
            output.write(' '.join(map(str, literals)) + ' 0\n')
        nc += len(additions)
        header = f'p cnf {nv} {nc}'
        if len(header) > HEADER_WIDTH:
            raise ValueError('DIMACS header exceeds reserved width')
        output.seek(0)
        output.write(header + ' ' * (HEADER_WIDTH - len(header)))
    meta['normalization'] = dict(npn_classes=len(reps), normalized_tables=sum(sizes),
                                 representatives=list(reps), orbit_sizes=list(sizes),
                                 helper_pins='strictly increasing, no constant; PI padding')
    with open(path + '.normalization.json', 'w') as output:
        json.dump(meta['normalization'], output, indent=2)
    return nv, nc, meta
