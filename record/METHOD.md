# Decoder synthesis by isolating shared LUTs

## Function class
The golden circuit's outputs are all 2^n minterms of its n <= 16 inputs (a decoder). `decsyn.py` reads the golden
AIGER with its own parser (`onehot.py`), checks the input count before building any truth table, computes every
output's truth table, and exits 3 for any other circuit; `generate.sh` then keeps the size start unchanged,
because the method does not apply there.

## Network
k shared LUTs Y_1..Y_k, each reading up to 6 inputs, and one LUT per output: LUTs = 2^n + k, levels = 2. The output
LUT for point q reads 6 signals A (inputs or shared LUTs) and is true exactly on q's code under A.

## Why it preserves function
That LUT is 1 at q and at every point carrying q's code under A, and 0 elsewhere. It is q's minterm exactly when q's
code is unique among all 2^n points (A isolates q). `decsyn.py` picks, per output, the first 6-subset (lexicographic)
that isolates its point, checks that the LUT is that minterm, and refuses to write otherwise. So the netlist equals
the golden on all 2^n patterns.

## Search
k ascends from the least feasible value: no shared LUT for n <= 6 (each output is one LUT); one for n = 7; two for
n >= 8, because one shared LUT cannot serve an 8-input decoder even when outputs may feed outputs (`bound.py`:
exhaustive CNF, CaDiCaL UNSATISFIABLE, refutation verified by cake_lpr), and every larger decoder contains that case.
- k <= 2: decided exactly. Permuting inputs maps a decoder to itself, so the shared LUTs' supports matter only through
  how many inputs they share. For each overlap (widest union first) the question "every point isolated, by both
  shared LUTs and 4 inputs or by one shared LUT and 5 inputs" is written as CNF over the two 64-bit truth tables
  (complement symmetry fixed by Y_i(0) = 0) and solved by CaDiCaL; a model is the network.
- k >= 3: simulated annealing over the shared LUTs' truth tables (bit flips) and supports (input swaps, 5% of moves)
  maximises the isolated points; seed 1, 60000 iterations per k, temperature 2.0 falling linearly to 0.05.
- Below the closed-form bound, the label construction in `onehot.py`: r raw and n - r selector inputs, each selector
  point labelled by a distinct t-subset (t = 6 - r) of k shared LUTs with C(k, t) >= 2^(n - r).
Every step is deterministic (fixed CNF and solver binary, fixed seed and iteration count).

## Result on dec (n = 8)
k = 2 with supports {0..5} and {2..7} is satisfiable: 256 + 2 = 258 LUTs at 2 levels. 257 LUTs is impossible at any
depth (`bound.py`) and one level is impossible (each output depends on 8 inputs), so 258 LUTs at 2 levels is optimal
on both axes for this circuit.
