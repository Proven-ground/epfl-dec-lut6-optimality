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
From a fresh checkout of this repository, on Linux with python3 and CaDiCaL on PATH. The benchmark is fetched from
the board at the pinned commit (sha256 `38def606e795975e469273411ee9217bc43656c57e6f6eeda3ea640452fa3443`):
```bash
curl -LO https://raw.githubusercontent.com/lsils/benchmarks/82d8cc6910419298e713a46644ed59fd3df53038/random_control/dec.aig
cd record/generator && python3 decsyn.py ../../dec.aig out.blif && sha256sum out.blif ../out.blif
```
writes `out.blif` deterministically (CaDiCaL on a fixed CNF; 6 to 8 minutes) and prints the same hash for both files,
`428d4987578e1714993052183f9d22af8275b1f39f79f6a17848392a005889f6`. `generate.sh` is the judge's wrapper around the
same call; its two trailing arguments are the board start netlists, used only when the circuit is not a decoder.
To recheck the bound, from the repository root:
```bash
gunzip -k bound_257.cnf.gz bound_257.lrat.gz && cake_lpr bound_257.cnf bound_257.lrat
```
