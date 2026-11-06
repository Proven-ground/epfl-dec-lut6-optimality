# A machine-checked proof that 257 LUT-6 nodes cannot compute the 8-input decoder

Lean 4 development proving the lower bound of the paper from the circuit model to the refutation. The theorem:

```lean
theorem DecoderOptimality.lowerBound (net : Network 8 6) (hdec : net.computesDecoder) :
    258 ≤ net.nodes.size
```

`Network 8 6` is any acyclic array of six-pin lookup tables over eight inputs, each pin reading a primary input, an
earlier node or a constant, directly or through an inverter, with an arbitrary table per node; `computesDecoder` says
that every one of the 256 minterms equals the function of some node, directly or through an output inverter. Asking
for a node loses no generality: a minterm is true on exactly one of the 256 patterns, a constant on none or all of
them, and an input, direct or inverted, on 128, so no decoder output is a constant or a wire. Nothing is assumed
about depth, fan-out or the node functions. Constants, buffers and inversions are therefore free, which is
the convention of the paper, and every node is a counted LUT.

## Axioms

`lake build DecoderOptimality.Main` ends with the line printed by `#print axioms` in `Main.lean`:

```
'DecoderOptimality.lowerBound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 DecoderOptimality.Certificate.cert_ok._native.native_decide.ax_1_1]
```

The fourth axiom is the one `native_decide` introduces for `cert_ok`: it records that the compiled evaluation of
`Std.Tactic.BVDecide.Reflect.verifyCert Bound.cnf cert` returned `true`, where `cert` is the LRAT file embedded at
compile time. The trusted base is Lean's kernel and, for that one evaluation, Lean's compiler together with the
definitions carrying `@[implemented_by]` that it runs (Lean's own description of `decide +native`). There is no
`sorry`, no other axiom, no external checker and no trusted solver; the lemmas of the paper and the correctness of
the encoder are theorems of this development.

`Main.lean` also prints the axioms of the two theorems that rest on Lemmas 1 and 2 alone:

```
'DecoderOptimality.lowerBound_general' depends on axioms: [propext, Classical.choice, Quot.sound]
'DecoderOptimality.lowerBound7' depends on axioms: [propext, Classical.choice, Quot.sound]
```

```lean
theorem lowerBound_general (net : Network n K) (hK : 1 ≤ K) (hnK : K < n) (hdec : net.computesDecoder) :
    2 ^ n + 1 ≤ net.nodes.size
theorem lowerBound7 (net : Network 7 6) (hdec : net.computesDecoder) : 129 ≤ net.nodes.size
```

## Modules

| module | content | paper |
|---|---|---|
| `Model.lean` | `Signal`, `Pin`, `Lut`, `Network`, `nodeFun`, `minterm`, `computesDecoder` | Section II, the model |
| `Lemma1.lean` | the first node computing each minterm; injective; `2 ^ n ≤ net.nodes.size` | Lemma 1 |
| `Lemma2.lean` | a node reading inputs, other minterms and constants through arbitrary inverters is not a minterm when `K < n` | Lemma 2 |
| `Reduced.lean` | classes `cls`, `Admissible`, the `Reduced` object | Section IV, the class and admissible pairs |
| `Structure.lean` | from a decoder network of at most `2 ^ n + 1` nodes to a `Reduced` object: the unique non-output node `Y`, its support `V`, an admissible pair per output; `two_pow_lt_size`, more than `2 ^ n` nodes from Lemmas 1 and 2 alone | the text between Lemmas 2 and 3 |
| `Dominance.lean` | admissible pairs with `F ⊆ V` and `|F| = base + u`, by strong induction on `|F|` | Lemma 3 |
| `Bits.lean` | points below 64 and their six bits | |
| `Encoder.lean` | the 64-point question as a `Std.Sat.CNF Nat` term in closed form | Section IV, the encoding |
| `Counter.lean` | Sinz's sequential counter is satisfied by the running count | the at-most-`u` bounds |
| `Assignment.lean` | an assignment from `Y`, a build order and a mask per point; five facts make every clause true | |
| `Bridge.lean` | any `Reduced 8 6` object yields a satisfying assignment: pad `V` to six inputs, read points as patterns, apply Lemma 3 | |
| `Certificate.lean` | `cert := include_str "../bound.lrat"`; `verifyCert Bound.cnf cert = true` by `native_decide`; `Bound.cnf.Unsat` | the refutation |
| `Main.lean` | `lowerBound`, `lowerBound_general`, `lowerBound7` and `#print axioms` | Theorem 1, the general bound, the 7-input decoder |
| `Emit.lean` | writes `Bound.cnf` as DIMACS with Lean's writer `Std.Sat.CNF.dimacs` | |

`DecoderOptimality.lean` imports the thirteen modules; `lakefile.toml` declares the library and the `emit` executable.

## The formula and its refutation

The formula the solver refutes is the DIMACS image of the same term `Bound.cnf` that the theorem connects to
networks; the writer is Lean's own, and `verifyCert` maps DIMACS variable `v` to atom `v - 1`, the inverse of the
writer. This encoder shares no code with `record/generator/bound.py`: atoms lie in fixed blocks and every option has
its own counter, so the instance is larger than the paper's while posing the same question.

| artefact | value |
|---|---|
| `bound.cnf` header | `p cnf 1318977 939074` |
| `bound.cnf` bytes, SHA-256 | 16554664, `6625d4f4cf15251a6d51de4c4f91fd1b4b5e86c61d2f0fad4f50ec7fe5f0b727` |
| solver | CaDiCaL rel-3.0.1, commit `c60730422e758ef1cebe7aeddf2dda31c996bf04`, `cadical -q --lrat --binary=false bound.cnf bound.lrat` |
| answer | `s UNSATISFIABLE`, exit 20, 8.5 s |
| `bound.lrat` bytes, SHA-256 | 34409273, `95fc046950c012b073edba638ea04fcdad3206a5eaed51c8fda9154dcc3b2c10` |

Both files are distributed compressed (`bound.cnf.gz`, `bound.lrat.gz`) and hashed after decompression.

cake_lpr accepts the same refutation of the same file, so the compiled evaluation inside Lean is not the only check
on it: `cake_lpr bound.cnf bound.lrat` prints `s VERIFIED UNSAT` in 4.0 s (cake_lpr commit
`a36874a8`, built from source on Debian 12, binary sha256 `72cd6fc6d93b5be1fd7de746113b033fa88c54e80c46a3d28f4aa6a3ec179c5d`). The record is `bound.cake_lpr.json`.

## Toolchain

| component | identity |
|---|---|
| Lean | `leanprover/lean4:v4.35.0` (`lean-toolchain`) |
| Mathlib | tag `v4.35.0`, commit `56a005855ea17e0b0958f73ec801ae140b0a1679` (`lake-manifest.json`) |
| LRAT checker | `Std.Tactic.BVDecide.LRAT.check`, soundness `check_sound`, shipped with the toolchain |
| cake_lpr | commit `a36874a8b750b43fe4b385b8ddbf5b033e46a3fa`, binary sha256 `72cd6fc6d93b5be1fd7de746113b033fa88c54e80c46a3d28f4aa6a3ec179c5d` (`bound.cake_lpr.json`) |

## Rebuild

From this folder, with `elan` installed (it reads `lean-toolchain`):

```bash
gunzip -k bound.lrat.gz
lake exe cache get
lake build DecoderOptimality.Main
```

The last command compiles the thirteen modules, checks the embedded refutation and prints the axiom line above. The
build requires an LRAT refutation of `Bound.cnf` accepted by Lean's checker. To regenerate the formula and the refutation:

```bash
lake exe emit bound.cnf && sha256sum bound.cnf
cadical -q --lrat --binary=false bound.cnf bound.lrat
```

Recorded run, 8 vCPU and 32 GiB, after `lake exe cache get`: the first `lake build` of the proof modules and the
formula writer (which compiles Mathlib's native code for the writer's imports) 841.9 s; a rebuild after an edit 74.7
to 164.9 s; `lake exe emit` 10.0 s; CaDiCaL 8.5 s; `lake build DecoderOptimality.Main` with the other modules built,
that is the certificate check and the final theorem, 122.6 s. `modal_lean.py` is the script that ran these steps.

## Source identities

SHA-256 of the sources as distributed.

| file | SHA-256 |
|---|---|
| `lakefile.toml` | `6ee22d1108dca85236d4d9de5b48f841951c463d38c8591537acef5d7a628fc0` |
| `lean-toolchain` | `ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c` |
| `lake-manifest.json` | `7a68d750906e2491458a6fdaa70108174c4e01f2c956c0a8107839e97663d023` |
| `DecoderOptimality.lean` | `2df29f6876aae239445746c925dedcc27edaaf19cf6bbf38bc506a5367af9ba8` |
| `Emit.lean` | `4d7687fa4b8383d8596bc7b2275e7703fc55cb06a1c487f159e2b5112120867e` |
| `DecoderOptimality/Assignment` | `2f35194ccbdebd2cb2e62ac6d662c6a19a06f730d51a35cd2f93270ed8418ea8` |
| `DecoderOptimality/Bits` | `62915d7462a7068c88c54420196b8208c398a0b8872df510618a13d0b876a865` |
| `DecoderOptimality/Bridge` | `53e343a12acf096f299d815fa50f1c3b52d72f309d6f4378c7d4349195a9d1a7` |
| `DecoderOptimality/Certificate` | `4d326dfa3e89323afd113299e70659ee3f2e98552208040ff809e6fdd70a344d` |
| `DecoderOptimality/Counter` | `5a0bd0e072ff82b6ba195587488a6f554c7c04c681dad74cfc61861bcc66b369` |
| `DecoderOptimality/Dominance` | `fb0b8bae5f4a6af91a64ffe2ce12cb6f90e8579bdb6fde38703d8fd32030d0d4` |
| `DecoderOptimality/Encoder` | `c068ed7f24e32a39b40dfd93b2d0fa45405a6d13b506f07c2243bfd6f498ce84` |
| `DecoderOptimality/Lemma1` | `e4ddab568be01d8925bcaefaea8e32e3d6c7bd9e17959296e7d2dc24ec3fd900` |
| `DecoderOptimality/Lemma2` | `4bc918e47a9e720a40f59965f4a2d9dfd1f4aa6326868e9c6bef23b7b9af8561` |
| `DecoderOptimality/Main` | `86813231b26797c648ec1484f3acc358642214de70e9e5bb43d8ccd0329d23ca` |
| `DecoderOptimality/Model` | `1e7248f5803ae2b5e0d37491546a053e2ff57c5820dc533d95740451b6df96d5` |
| `DecoderOptimality/Reduced` | `51631e66aafafd5854aed28bc05c5f5abef6c17421b792e86ca3b02a6574ee69` |
| `DecoderOptimality/Structure` | `a7309cdf3658047a1cc51eff79d5a78933bb8837dbe009c95e1edc7d929f99f2` |
