# Decoder family: 36, 67 and 130 LUTs

| LUT size K | Decoder inputs | Minimum at any depth | Depth of that circuit | Minimum at two levels |
|---|---:|---:|---:|---:|
| 3 | 5 | 36 | 3 | 37 |
| 4 | 6 | 67 | 2 | 67 |
| 5 | 7 | 130 | 3 | 131 |

Every circuit was simulated on every input, then read back and checked with a separate BLIF evaluator. The next-smaller counts (35, 66 and 129) have LRAT refutations accepted by cake_lpr. The two-level lower bounds cover every helper support class: 17 cases at K=3, three at K=5. K=4 already meets its unrestricted minimum at two levels.

The new reduction removes output-to-output connections by replacing each minterm pin with one distinguishing primary input. It then asks only whether each minterm has an isolating code from primary inputs and available helpers. Helpers can still read decoder outputs. First-helper NPN normalization and sorted helper pins remove equivalent searches. The full completeness arguments are in PROTOCOL.md. They are written mathematical arguments; the new multi-helper reduction and its encoder are not yet proved in Lean.

GenericLift.lean is checked against the existing Lean project. It lifts a one-helper reduced object from (n,K) to (n+1,K+1), preserving its contradiction. With the existing 8-input theorem this proves unrestricted lower bounds 34, 66 and 130 for K=3,4,5. The lift uses only the three standard axioms; its lower-bound theorems also inherit the existing certificate's native_decide axiom. Thus K=5's 130 lower bound is machine-checked. The stronger 36 and 67 bounds use the new written reduction and checked LRAT refutations. No new Lean theorem is claimed for those stronger bounds.

## Replay the supplement

Extract decoder-family-supplement.zip, then run:

```sh
python verify_release.py --cake-lpr /absolute/path/to/cake_lpr
```

This verifies the manifest and exact case inventory, exhaustively evaluates all five circuits, replays all 23 certificates, and requires rejection of missing circuits, missing or duplicated certificates, a changed minterm and a malformed certificate. Acceptance requires the literal `s VERIFIED UNSAT` line and a successful exit. A zero exit alone is insufficient: cake_lpr can return zero while reporting a failed check.

The package includes DATA.json with exact artifact paths and decompressed hashes, all netlists, compressed formulas and LRAT files, the encoder sources and the mathematical bridge. Tool pins are CaDiCaL c60730422e758ef1cebe7aeddf2dda31c996bf04 and cake_lpr a36874a8b750b43fe4b385b8ddbf5b033e46a3fa. No solver is needed for replay.

To regenerate the new small formulas on Modal:

```sh
python -m modal run modal_closure.py --stage sym-qualify
python -m modal run modal_closure.py --stage sym-search --k 3 --extra 3 --seconds 120
python -m modal run modal_closure.py --stage sym-search --k 4 --extra 2 --seconds 120
```

These commands use paid Modal compute and the configured account. Stored records bind results to their actual source revisions; later runner edits do not relabel earlier runs.
