"""Unrestricted decoder synthesis after eliminating output-to-output pins.

An output minterm can be isolated without reading other output minterms: each
such signal distinguishes at most its one pattern from the target, and one
primary-input bit can distinguish that pattern too. Rebuild the output LUT as
the single row of its target. No helper edge is added, so acyclicity is preserved.

Helpers may still read earlier output minterms. Their selected output signals
must have an isolation witness using only earlier helpers. This prefix-witness
condition replaces output-order variables and collision-cardinality counters.
The decoder chooses the witness with the earliest last helper for each output.
"""
import itertools

from direct_multi import Writer, read_model, simulate, topological


def build(path, K, n, extra, plant=None):
    if not 1 <= K < n or extra < 1:
        raise ValueError('requires n>K and positive helper count')
    P = 1 << n
    writer = Writer(path)
    new, clause = writer.new, writer.clause
    tables = [[new() for _ in range(1 << K)] for _ in range(extra)]
    for table in tables:
        clause([-table[0]])
    values = [[tables[0][x & ((1 << K) - 1)] for x in range(P)]]
    values += [[new() for _ in range(P)] for _ in range(extra - 1)]
    selectors = [None]
    required_prefixes = []
    for helper in range(1, extra):
        candidates = list(range(n + 1)) + [n + 1 + q for q in range(P)]
        candidates += [n + 1 + P + h for h in range(helper)]
        pins = []
        for pin in range(K):
            selected = {signal: new() for signal in candidates}
            pins.append(selected)
            choices = list(selected.values())
            clause(choices)
            prefix = None
            for choice in choices[:-1]:
                following = new()
                clause([-choice, following])
                if prefix is not None:
                    clause([-prefix, following])
                    clause([-choice, -prefix])
                prefix = following
            clause([-choices[-1], -prefix])
            required_prefixes.extend((selected[n + 1 + q], q, helper) for q in range(P))
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
        for helper, table in enumerate(plant['tables']):
            for bit, variable in enumerate(tables[helper]):
                clause([variable if (table >> bit) & 1 else -variable])
            if helper:
                for pin, signal in enumerate(plant['pins'][helper]):
                    clause([selectors[helper][pin][signal]])

    differences = {}

    def different(a, b):
        if a == b:
            return None
        key = (min(a, b), max(a, b))
        if key not in differences:
            variable = new()
            clause([-variable, a, b])
            clause([-variable, -a, -b])
            differences[key] = variable
        return differences[key]

    options = [[] for _ in range(P)]
    for q in range(P):
        for count in range(1, min(extra, K) + 1):
            for shared in itertools.combinations(range(extra), count):
                for raw in itertools.combinations(range(n), K - count):
                    option = new()
                    options[q].append((option, shared, raw))
                    free = [i for i in range(n) if i not in raw]
                    for mask in range(1, 1 << len(free)):
                        x = q ^ sum(1 << i for bit, i in enumerate(free) if (mask >> bit) & 1)
                        differ = [different(values[h][q], values[h][x]) for h in shared]
                        clause([-option] + [literal for literal in differ if literal is not None])
        clause([option for option, shared, raw in options[q]])
    for selected, q, helper in required_prefixes:
        clause([-selected] + [option for option, shared, raw in options[q] if max(shared) < helper])
    writer.close()
    return writer.nv, writer.nc, dict(K=K, n=n, P=P, extra=extra, tables=tables,
                                      values=values, selectors=selectors, options=options)


def decode(model, meta):
    K, n, P, extra = (meta[key] for key in ('K', 'n', 'P', 'extra'))
    outputs = []
    for q, options in enumerate(meta['options']):
        valid = [option for option in options if model.get(option[0])]
        if not valid:
            raise ValueError('output has no isolation witness')
        option, shared, raw = min(valid, key=lambda option: (max(option[1]), option[1], option[2]))
        pins = list(raw) + [n + 1 + P + helper for helper in shared]
        bits = [(q >> i) & 1 for i in raw]
        bits += [int(bool(model.get(meta['values'][helper][q]))) for helper in shared]
        row = sum(bit << i for i, bit in enumerate(bits))
        outputs.append((pins, 1 << row))
    helpers = []
    for helper in range(extra):
        pins = list(range(K)) if helper == 0 else []
        if helper:
            for selected in meta['selectors'][helper]:
                choices = [signal for signal, variable in selected.items() if model.get(variable)]
                if len(choices) != 1:
                    raise ValueError('helper pin is not one-hot')
                pins.append(choices[0])
        table = sum(1 << bit for bit, variable in enumerate(meta['tables'][helper]) if model.get(variable))
        helpers.append((pins, table))
    nodes = outputs + helpers
    order = topological(nodes, n, K)
    if order is None:
        raise ValueError('prefix witnesses failed to produce an acyclic network')
    return nodes, order
