# dec: 258 LUTs at 2 levels (EPFL board size record: 264 LUTs, 2 levels, 2018)

The 8-input decoder of the EPFL combinational benchmark suite in 258 6-input LUTs at 2 levels, 6 LUTs below the
board's size record, which had stood since 2018. 257 LUTs is impossible at any depth, so 258 LUTs at 2 levels is
optimal on both axes.

## Result
- Netlist: `record/out.blif` (candidate identity `c99a2dd1fe0de588b36cdc4019f52d578d1a608d419f9d5f311f5bb0b7027713`).
- Method: two shared LUTs (inputs 0..5 and 2..7) found by exact SAT synthesis; each of the 256 outputs reads 6 of the
  10 signals under which its point's code is unique. `record/METHOD.md`, generator in `record/generator/`.
- Judge (frozen, sha256 `d37078e4...7f7a1`): checker A (ABC `cec`) EQUIVALENT in 1.8 s; checker B (SAT sweep with every
  lemma checked by the repository's LRAT kernel and by cake_lpr) EQUIVALENT, 256 of 256 lemmas certified, evidence
  `record/lemmas.tar.gz`; class RECORD on the size axis (ledger `s000007`, `s000007p`).
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
because every output depends on all 8 inputs. Every hash, command and answer is in `verdicts.json`.

## Reproduce
From `record/generator/`, in Linux with python3 and CaDiCaL on PATH:
```bash
bash generate.sh dec ../../../../benchmarks/golden/dec.aig ../../../../state/starts/dec_size.blif ../../../../state/starts/dec_depth.blif
```
writes `out.blif` deterministically (CaDiCaL on a fixed CNF; about 6 minutes). To recheck the bound:
```bash
gunzip -k bound_257.cnf.gz bound_257.lrat.gz && cake_lpr bound_257.cnf bound_257.lrat
```
