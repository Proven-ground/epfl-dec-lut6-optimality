"""Decoder reduction for any number of non-output LUTs.

The earliest helper reads only primary inputs, by Lemma 2. Remaining helpers
may read earlier helpers and any earlier output. An output's selected helpers
and primary inputs leave a collision class. Its other pins must name every
other point in that class, and those minterm outputs must precede it. Bounding
the class and enforcing that order is necessary and sufficient for that output.
The complete normalization and reduction argument is recorded in PROTOCOL.md.
"""
import itertools

from direct_multi import Writer, read_model, simulate, topological


def build(path, K, n, extra, plant=None):
    if not 1 <= K < n or extra < 1:
        raise ValueError('requires n>K and at least one helper')
    P = 1 << n
    writer = Writer(path)
    new, clause = writer.new, writer.clause
    tables = [[new() for _ in range(1 << K)] for _ in range(extra)]
    for table in tables:
        clause([-table[0]])
    values = [[tables[0][x & ((1 << K) - 1)] for x in range(P)]]
    values += [[new() for _ in range(P)] for _ in range(extra - 1)]
    rank_nodes = P + extra - 1
    before = {(a, b): new() for a in range(rank_nodes) for b in range(a + 1, rank_nodes)}

    def prec(a, b):
        return before[(a, b)] if a < b else -before[(b, a)]

    for a, b, c in itertools.permutations(range(rank_nodes), 3):
        clause([-prec(a, b), -prec(b, c), prec(a, c)])
    for a in range(1, extra):
        for b in range(a + 1, extra):
            clause([prec(P + a - 1, P + b - 1)])
    for q in range(1, P):
        clause([prec(0, q)])
    first_helpers = None if plant is None else plant.get('first_output_helpers')
    if first_helpers is not None:
        if not 1 <= first_helpers <= extra:
            raise ValueError('invalid number of helpers before the first output')
        if first_helpers > 1:
            clause([prec(P + first_helpers - 2, 0)])
        if first_helpers < extra:
            clause([prec(0, P + first_helpers - 1)])
        if first_helpers == 1 and n == K + 2 and K >= 3:
            # Output zero reads only the first helper and primary inputs. Its
            # three free support coordinates can be permuted to the final three.
            # With table[0]=0, all seven other points of that face must be one.
            for mask in range(1, 8):
                clause([tables[0][mask << (K - 3)]])
    quarter_normalization = K == 3 and n == 5 and first_helpers == 1 and extra >= 2
    if quarter_normalization:
        # These four minterms each read helper zero and the two outside inputs.
        # Recompute them that way and move them before helper one, at no node cost.
        for q in range(P):
            if q & 7 == 0:
                clause([prec(q, P)])

    def at_most(literals, bound):
        if bound >= len(literals):
            return
        if bound == 0:
            for literal in literals:
                clause([-literal])
            return
        states = [[new() for _ in range(bound)] for _ in literals]
        for i, literal in enumerate(literals):
            clause([-literal, states[i][0]])
            if i:
                for j in range(bound):
                    clause([-states[i - 1][j], states[i][j]])
                for j in range(1, bound):
                    clause([-literal, -states[i - 1][j - 1], states[i][j]])
                clause([-literal, -states[i - 1][bound - 1]])

    selectors = [None]
    for helper in range(1, extra):
        # Signal numbering agrees with the direct circuit encoder.
        candidates = list(range(n + 1))
        candidates += [n + 1 + q for q in range(P)]
        candidates += [n + 1 + P + h for h in range(helper)]
        pins = []
        for pin in range(K):
            selected = {signal: new() for signal in candidates}
            pins.append(selected)
            clause(list(selected.values()))
            at_most(list(selected.values()), 1)
            for q in range(P):
                clause([-selected[n + 1 + q], prec(q, P + helper - 1)])
                if quarter_normalization and helper == 1 and q & 7 != 0:
                    # Before helper one, an earliest non-quarter minterm cannot
                    # be isolated by helper zero, primaries and quarter minterms.
                    clause([-selected[n + 1 + q]])
        selectors.append(pins)
        pin_values = [[new() for _ in range(P)] for _ in range(K)]
        for pin, selected in enumerate(pins):
            for x in range(P):
                ones = [selected[i] for i in range(n) if (x >> i) & 1]
                ones.append(selected[n + 1 + x])
                dynamic = [(selected[n + 1 + P + h], values[h][x]) for h in range(helper)]
                result = pin_values[pin][x]
                clause([-result] + ones + [choice for choice, value in dynamic])
                for choice in ones:
                    clause([-choice, result])
                for choice, value in dynamic:
                    clause([-choice, -result, value])
                    clause([-choice, result, -value])
        for x in range(P):
            for row in range(1 << K):
                guard = [-pin_values[pin][x] if (row >> pin) & 1 else pin_values[pin][x]
                         for pin in range(K)]
                clause(guard + [-values[helper][x], tables[helper][row]])
                clause(guard + [values[helper][x], -tables[helper][row]])
    if plant is not None and 'tables' in plant:
        if len(plant['tables']) != extra:
            raise ValueError('incorrect planted helper count')
        for helper, table in enumerate(plant['tables']):
            for bit, variable in enumerate(tables[helper]):
                clause([variable if (table >> bit) & 1 else -variable])
            if helper:
                for pin, signal in enumerate(plant['pins'][helper]):
                    clause([selectors[helper][pin][signal]])

    equality = {}

    def equal(a, b):
        if a == b:
            return None
        key = (min(a, b), max(a, b))
        if key not in equality:
            variable = new()
            clause([-variable, -a, b])
            clause([-variable, a, -b])
            clause([variable, a, b])
            clause([variable, -a, -b])
            equality[key] = variable
        return equality[key]

    helper_sets = [shared for count in range(1, min(K, extra) + 1)
                   for shared in itertools.combinations(range(extra), count)]
    options = []
    for q in range(P):
        choices = []
        for shared in helper_sets:
            if shared == (0,):
                # Lemma 3 applies whenever only the input-only first helper is read.
                base = n - K + 1
                raw_choices = []
                for bound in range(K - base + 1):
                    for free in itertools.combinations(range(K), base + bound):
                        raw = tuple(i for i in range(n) if i not in free)
                        raw_choices.append((raw, bound))
            else:
                raw_choices = [(raw, K - len(shared) - count)
                               for count in range(K - len(shared) + 1)
                               for raw in itertools.combinations(range(n), count)]
            for raw, bound in raw_choices:
                option = new()
                choices.append(option)
                if q == 0 and first_helpers is not None:
                    if max(shared) != first_helpers - 1:
                        clause([-option])
                    else:
                        # Retiming puts only ancestors of output zero before it.
                        # Every earlier helper either is read directly or has a
                        # reader among these later ancestral helpers.
                        for helper in range(first_helpers - 1):
                            if helper not in shared:
                                readers = [selectors[reader][pin][n + 1 + P + helper]
                                           for reader in range(helper + 1, first_helpers)
                                           for pin in range(K)]
                                clause([-option] + readers)
                if quarter_normalization and q & 7 == 0 and shared == (0,) and raw == (3, 4):
                    clause([option])
                for helper in shared:
                    if helper:
                        clause([-option, prec(P + helper - 1, q)])
                free = [i for i in range(n) if i not in raw]
                guards = []
                for mask in range(1, 1 << len(free)):
                    x = q ^ sum(1 << i for bit, i in enumerate(free) if (mask >> bit) & 1)
                    same = [equal(values[h][q], values[h][x]) for h in shared]
                    same = [literal for literal in same if literal is not None]
                    if same:
                        guard = new()
                        clause([-guard, option])
                        for literal in same:
                            clause([-guard, literal])
                        clause([guard, -option] + [-literal for literal in same])
                    else:
                        guard = option
                    guards.append(guard)
                    clause([-guard, prec(x, q)])
                at_most(guards, bound)
                options.append((q, option, shared, raw, bound))
        clause(choices)
    writer.close()
    return writer.nv, writer.nc, dict(K=K, n=n, P=P, extra=extra, tables=tables,
                                      values=values, selectors=selectors, options=options)


def decode(model, meta):
    K, n, P, extra = (meta[key] for key in ('K', 'n', 'P', 'extra'))
    helpers = []
    for helper in range(extra):
        pins = list(range(K)) if helper == 0 else []
        if helper:
            for selected in meta['selectors'][helper]:
                matches = [signal for signal, variable in selected.items() if model.get(variable)]
                if len(matches) != 1:
                    raise ValueError('pin selector is not one-hot')
                pins.append(matches[0])
        table = sum(1 << bit for bit, variable in enumerate(meta['tables'][helper]) if model.get(variable))
        helpers.append((pins, table))
    output_nodes = [None] * P
    for q, option, shared, raw, bound in meta['options']:
        if output_nodes[q] is not None or not model.get(option):
            continue
        members = [x for x in range(P) if x != q and all(((x ^ q) >> i) & 1 == 0 for i in raw)
                   and all(bool(model.get(meta['values'][h][q])) == bool(model.get(meta['values'][h][x]))
                           for h in shared)]
        if len(members) > bound:
            raise ValueError('decoded collision class exceeds the pin budget')
        pins = list(raw) + [n + 1 + P + h for h in shared] + [n + 1 + x for x in members]
        pins += [n] * (K - len(pins))
        bits = [(q >> i) & 1 for i in raw]
        bits += [int(bool(model.get(meta['values'][h][q]))) for h in shared]
        bits += [0] * (K - len(bits))
        row = sum(bit << i for i, bit in enumerate(bits))
        output_nodes[q] = (pins, 1 << row)
    if any(node is None for node in output_nodes):
        raise ValueError('model has no option for an output')
    nodes = output_nodes + helpers
    order = topological(nodes, n, K)
    if order is None:
        raise ValueError('decoded graph is cyclic')
    return nodes, order
