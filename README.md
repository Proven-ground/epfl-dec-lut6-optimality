# dec: 258 LUTs at 2 levels (EPFL board size record: 264 LUTs, 2 levels, 2018)

The 8-input decoder of the EPFL combinational benchmark suite in 258 6-input LUTs at 2 levels, 6 LUTs below the
board's size record, which had stood since 2018. 257 LUTs is impossible at any depth, so 258 LUTs at 2 levels is
optimal on both axes.

## Result
- Netlist: `record/out.blif` (candidate identity `c99a2dd1fe0de588b36cdc4019f52d578d1a608d419f9d5f311f5bb0b7027713`).
- Method: two shared LUTs (inputs 0..5 and 2..7) found by exact SAT synthesis; each of the 256 outputs reads 6 of the
  10 signals under which its point's code is unique. `record/METHOD.md`, generator in `record/generator/`.
- Judge (frozen, sha256 `d37078e4...7f7a1`): checker A (ABC `cec`) EQUIVALENT in 1.8 s wall time (ABC reports 1.33 s);
  checker B (SAT sweep with every lemma checked by the repository's LRAT kernel and by cake_lpr) EQUIVALENT, 256 of 256
  lemmas certified, evidence `record/lemmas.tar.gz`; class RECORD on the size axis (ledger `s000007`, `s000007p`).
- Reproduced: the stored generator, rerun by the judge server in a fresh runner, produced the same candidate identity
  (ledger `rc99a2dd1fe0d`, 489 s, 172.6 MB peak).
- Re-verified outside the server: store intact, checker A and checker B EQUIVALENT, reproduction identical: confirmed.
- Transferred to all five sealed circuits (arbiter, div, mem_ctrl, router, voter): generator OK and checker A
  EQUIVALENT on each; the method applies only to decoders, so it keeps their size starts.

## Optimality
All 256 outputs are distinct minterms, so each needs its own LUT; a 257-LUT network has exactly one other LUT.
`record/generator/bound.py` reduces "one other LUT suffices" to a finite question and writes it as CNF
(`bound_257.cnf.gz`). CaDiCaL answers UNSATISFIABLE and its LRAT refutation (`bound_257.lrat.gz`) is verified by
cake_lpr: `s VERIFIED UNSAT`. Control: `bound_base.py` with BASE = 2 writes the same encoding for the 7-input decoder,
which CaDiCaL answers SATISFIABLE; BASE = 3 writes the bound instance clause for clause. One level is impossible
because every output depends on all 8 inputs. The hashes, commands and answers of the main result are in
`verdicts.json`.

## Machine-checked proof of the bound
`lean/` is a Lean 4 development (toolchain `leanprover/lean4:v4.35.0`, Mathlib commit `56a00585`) that proves the
lower bound from the circuit model to the refutation:
```lean
theorem DecoderOptimality.lowerBound (net : Network 8 6) (hdec : net.computesDecoder) : 258 ≤ net.nodes.size
```
A `Network 8 6` is any acyclic array of six-pin LUTs over eight inputs, each pin reading an input, an earlier node or a
constant through an optional inverter, with an arbitrary table per node; `computesDecoder` says every minterm equals
some node's function up to an output inverter; asking for a node loses nothing, since a minterm is true on exactly
one of the 256 patterns while a constant is true on none or all of them and an input, direct or inverted, on 128. The three lemmas of the paper are theorems of the development; a
second encoder, written in Lean and sharing no code with `bound.py`, produces the formula `lean/bound.cnf.gz`
(939,074 clauses), and the theorem that every network of at most 257 nodes satisfies it; CaDiCaL's LRAT refutation
`lean/bound.lrat.gz` is checked by Lean's own verified LRAT checker inside the proof. `#print axioms` lists `propext`,
`Classical.choice`, `Quot.sound` and the one axiom `native_decide` introduces for that check; no `sorry`. With `elan`
installed, from `lean/`:
```bash
gunzip -k bound.lrat.gz && lake exe cache get && lake build DecoderOptimality.Main
```
The build ends with the axiom line; it requires an LRAT refutation of `Bound.cnf` accepted by Lean's checker. `lean/README.md` lists every module, the
hashes of the sources, the formula and the certificate, and the recorded run. The same file also proves, from
Lemmas 1 and 2 alone and under the three standard axioms, `lowerBound_general`: every decoder network over `n > K ≥ 1`
inputs has at least `2 ^ n + 1` nodes, and its instance `lowerBound7`: 129 LUT-6 nodes for the 7-input decoder.
cake_lpr accepts the Lean-written formula's refutation too (`cake_lpr bound.cnf bound.lrat`, `s VERIFIED UNSAT`,
4.0 s, `lean/bound.cake_lpr.json`).

## The family n = K + 2
For K = 3, 4, 5 and n = K + 2 the reduction's instance (`crosscheck/reduced_bound.py K n`) is refuted by CaDiCaL with an
LRAT proof that cake_lpr accepts, so 2^n + 1 LUT-K nodes are impossible for the (K+2)-input decoder, as for K = 6.
The two-shared-LUT construction of the 258-LUT netlist does not transfer: the isolation instance with two shared
LUT-K nodes (`family/family.py K n`), one formula per overlap of the two supports, is unsatisfiable in every case,
while the same encoder finds the one- and two-shared-LUT networks at K = 6 for 7 and 8 inputs (`family/K6_n7.*`,
`family/K6_n8.*`, the positive controls: n = 7 in 0.0 s, n = 8 in 58.1 s). At K = 6 the count is
2^n + 2 = 258; the exact counts at K = 3, 4, 5, reached with more helpers or a third level, are in the section below.

| K | n | reduced instance | CaDiCaL | cake_lpr | two shared LUTs (overlaps) |
|---|---|---|---|---|---|
| 3 | 5 | 128 variables, 737 clauses | UNSAT, 0.0 s | `s VERIFIED UNSAT`, 0.0 s | unsatisfiable for overlaps 1, 2, 3, at most 0.0 s |
| 4 | 6 | 1264 variables, 7745 clauses | UNSAT, 0.0 s | `s VERIFIED UNSAT`, 0.0 s | unsatisfiable for overlaps 2, 3, 4, at most 0.0 s |
| 5 | 7 | 11552 variables, 68257 clauses | UNSAT, 0.1 s | `s VERIFIED UNSAT`, 0.1 s | unsatisfiable for overlaps 3, 4, 5, at most 35.9 s |

`family/K<K>_n<n>.json` holds every hash, size, time and answer; `family/reduced_K<K>_n<n>.cnf.gz` and `.lrat.gz` are
the certified refutations; `family/modal_family.py` ran the three cases, the controls and the cake_lpr check of the Lean
formula. To rerun one case, from this folder:
```bash
python3 crosscheck/reduced_bound.py reduced.cnf 5 7 && cadical -q --lrat --binary=false reduced.cnf reduced.lrat; cake_lpr reduced.cnf reduced.lrat
python3 family/family.py 5 7 iso && for f in iso_*.cnf; do cadical -q $f; done
```
The first line prints `s VERIFIED UNSAT`; every `cadical` of the second exits with status 20.


## Reproduce the main result
From a fresh checkout of this repository, on Linux with python3, ABC, cake_lpr and CaDiCaL on PATH. The benchmark is
fetched from the board at the pinned commit (sha256 `38def606e795975e469273411ee9217bc43656c57e6f6eeda3ea640452fa3443`):
```bash
curl -LO https://raw.githubusercontent.com/lsils/benchmarks/82d8cc6910419298e713a46644ed59fd3df53038/random_control/dec.aig
```
Equivalence and size, with ABC: `nd = 258`, `lev = 2`, `Networks are equivalent`.
```bash
abc -c "read_blif record/out.blif; print_stats; cec dec.aig record/out.blif"
```
Equivalence and structure, by exhaustive simulation with readers written for this check only (no code shared with
the generator): 256 of 256 outputs match on all 256 patterns, every node has six inputs, none is a constant, buffer
or inverter, depth 2.
```bash
python3 simulate_dec.py dec.aig record/out.blif
```
The bound. The verdict is the printed line `s VERIFIED UNSAT`: cake_lpr exits with status 0 also when it rejects a
proof, so its exit status is not the verdict.
```bash
gunzip -k bound_257.cnf.gz bound_257.lrat.gz && cake_lpr bound_257.cnf bound_257.lrat
```
The stored instance has CRLF line endings; with carriage returns removed it equals what `bound.py` writes (both lines
print `6b9bb19466070c2eead23fa4448d75ec1b79159a520755db6be2348f1ead7c3d`):
```bash
python3 record/generator/bound.py b.cnf && tr -d "\r" < b.cnf | sha256sum && tr -d "\r" < bound_257.cnf | sha256sum
```
The netlist itself, regenerated deterministically (CaDiCaL on a fixed CNF; 354 to 489 s in the recorded runs); both
hashes print `428d4987578e1714993052183f9d22af8275b1f39f79f6a17848392a005889f6`:
```bash
cd record/generator && python3 decsyn.py ../../dec.aig out.blif && sha256sum out.blif ../out.blif
```
`generate.sh` is the judge's wrapper around the same call; its two trailing arguments are the board start netlists,
used only when the circuit is not a decoder.

## The witness partition
Each of the 256 patterns is isolated by exactly one of the two shared LUTs with five raw inputs, Y0 exactly where
`count[2] = count[4]`. Prints 128 and 128, both 0, neither 0, and `holds`:
```bash
python3 partition.py
```

## Larger decoders
Two-level upper bounds for the 9- to 12-input decoders: builds each network (label construction for 9 and 10 inputs,
block construction for 11 and 12) and checks it by exhaustive simulation: 521, 1036, 2068 and 4120 LUTs, two levels,
fan-in at most six, no mismatching output.
```bash
python3 larger_decoders.py
```

## Cross-check of the reduction
`crosscheck/` holds the paper's reduction parametrised by LUT size K and decoder inputs n (`reduced_bound.py`;
with K = 6 it writes the stored 8-input instance and the 7-input control clause for clause), a direct circuit
encoding that assumes only that each output is its own node (`direct_roles.py`: free fanins, free tables, free
build order, every model decoded and simulated in an order recomputed from its fanins), a fully direct encoding with
free node roles for the tiniest case (`direct_bound.py`), and the driver. With CaDiCaL at CADICAL:
```bash
python3 crosscheck/run_crosscheck.py CADICAL
```
runs six (K, n) cases with 2^n and 2^n + 1 LUTs plus positive controls, judges every comparison, and ends with one
line of counts. A decoded network that is not a decoder, or an answer contrary to the expected one, is a violation;
a solver that times out is incomplete. The run exits 1 on any violation, 2 when a comparison is incomplete, and 0
only when every comparison was decided and held. `crosscheck/RESULTS.txt` is the recorded run: every comparison held,
0 violations, 0 incomplete. The direct encoder refutes 2^n LUTs in every case, and for 2^n + 1 the two encoders agree
in all six, including K = 4, n = 5 and K = 5, n = 6, where a network exists, is found and is admitted by the reduction.

The case K = 5, n = 7 was run separately (`python3 crosscheck/direct_roles.py OUT.cnf 5 7 1`, then CaDiCaL: 129
nodes, 20.2 million clauses, UNSATISFIABLE in 6229 s with a 3.72 GiB peak; `python3 crosscheck/reduced_bound.py OUT.cnf
5 7`: UNSATISFIABLE in 1.5 s); the solver outputs are in `crosscheck/RESULTS_5_7.txt`. Both encoders refute,
consistent. The case K = 6, n = 7 was solved on Modal with `crosscheck/modal_solve.py` (one container per seed, results
cached by encoder hash, case, seed and solver commit; a job whose network fails simulation is reported invalid and the
run exits non-zero): the direct instance (308,696 variables, 24.3 million clauses) has a 129-node network, found with
seed 1 in 2604 s and simulated with zero mismatches; the reduced instance for that case is the satisfiable 7-input
control. `crosscheck/RESULTS_6_7.json` holds the run record and the decoded network; every output reads the extra
node, which reads six inputs only. The 2^n-LUT direct instances for K = 5, n = 7 and K = 6, n = 7 were also run on
Modal and are refuted in 14 s and 29 s, as Lemma 2 predicts; `crosscheck/RESULTS_n7_2n.json` holds both run records.

The encoding itself is tested by planting known networks into it. The paper's 7-input construction (one shared LUT
over inputs 0 to 5 with table `0x000ff0ffff0ff000`, 129 LUTs) is built, checked by exhaustive simulation, planted at
K = 6, and admitted (`crosscheck/RESULTS_plant_witness.txt`):
```bash
python3 crosscheck/plant_witness.py CADICAL WORKDIR
```

## Exact family counts for K = 3, 4, 5

The family supplement `decoder-family-supplement.zip` (173,619,481 bytes, SHA-256
`f1487ad8b25ab08bb65bc0c556ca6767b213f7c6b8e2385d51c4fe2703b57145`) is attached to this repository's release; its
files other than the compressed formulas and refutations are in `family_closure/`.
The (K+2)-input decoder minima are 36, 67 and 130 LUT-K nodes, attained at depths 3, 2 and 3.
At depth two the exact counts are 37, 67 and 131. All five netlists pass exhaustive replay;
all 23 retained LRAT refutations pass cake_lpr. The new multi-helper reduction and its NPN
normalization are written mathematical proofs, documented in the supplement's PROTOCOL.md.
GenericLift.lean proves the 130 lower bound in Lean through the existing one-helper theorem;
the stronger K3/36 and K4/67 reductions have not yet been machine-checked.

After extracting the supplement:

```sh
python verify_release.py --cake-lpr /absolute/path/to/cake_lpr
```

## Tests that every check fails on a broken input
Every script that issues a verdict has tests that break its input on purpose and require the verdict to fail:
swapped outputs, a buffer, a seventh LUT input, a third level, a missing output, a changed shared table, a cyclic
network, a timed-out solver; for the encoding, a known network with shuffled pins must be admitted and the same
network with two outputs swapped must be refuted. They run against the real solver, with Python's optimised mode on
so that no check rests on `assert`:
```bash
python3 -O -m unittest test_checks.py
cd crosscheck && CADICAL=/path/to/cadical python3 -O -m unittest test_run_crosscheck.py
```
`test_checks.py` needs the benchmark fetched above as `dec.aig` in the repository root (or `DEC_AIG` set to it).
