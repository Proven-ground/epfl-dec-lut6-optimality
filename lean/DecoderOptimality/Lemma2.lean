import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import DecoderOptimality.Model

/-!
# Lemma 2 of the paper: an output node that reads only inputs and other outputs is not a minterm

Stated abstractly. A pin of the node for pattern `q` reads a primary input, the minterm of a pattern
`p ≠ q` (another output), or a constant, each possibly through an inverter. The node applies an
arbitrary table to its `K` pin values and may be read through an output inverter. When `K < n`, the
resulting function is not the minterm of `q`.

Proof. Let `R` be the inputs read by input pins and `U` their complement; `P` the patterns read through
other-output pins. `|R| + |P| ≤ K < n`, so `|U| = n - |R| > |P|`. Flipping `q` at each `i ∈ U` gives `|U|`
distinct patterns, so some flipped pattern `x` is outside `P`. At `x` every pin reads what it reads at `q`:
the flipped input is unread, every other-output minterm is 0 at both, constants are constant. So the node
takes the same value at `x` and at `q`, while the minterm of `q` does not, and neither does its complement.
-/

namespace DecoderOptimality

open Finset

/-- What a pin of the node for `q` may read. -/
inductive Read (n : Nat) (q : Fin n → Bool) where
  | input (i : Fin n) (neg : Bool)
  | other (p : Fin n → Bool) (hp : p ≠ q) (neg : Bool)
  | const (b : Bool)

variable {n K : Nat} {q : Fin n → Bool}

/-- The value a pin delivers at input pattern `x`. -/
def Read.eval : Read n q → (Fin n → Bool) → Bool
  | .input i neg, x => Bool.xor neg (x i)
  | .other p _ neg, x => Bool.xor neg (minterm p x)
  | .const b, _ => b

/-- The input a pin reads, if it reads one. -/
def Read.inputIdx : Read n q → Option (Fin n)
  | .input i _ => some i
  | .other _ _ _ => none
  | .const _ => none

/-- The pattern a pin reads the minterm of, if it reads one. -/
def Read.otherPat : Read n q → Option (Fin n → Bool)
  | .input _ _ => none
  | .other p _ _ => some p
  | .const _ => none

/-- Pins that read a primary input. -/
def inputPins (pins : Fin K → Read n q) : Finset (Fin K) :=
  univ.filter fun p => ((pins p).inputIdx).isSome = true

/-- Pins that read another output. -/
def otherPins (pins : Fin K → Read n q) : Finset (Fin K) :=
  univ.filter fun p => ((pins p).otherPat).isSome = true

theorem pins_card (pins : Fin K → Read n q) : (inputPins pins).card + (otherPins pins).card ≤ K := by
  have hdisj : Disjoint (inputPins pins) (otherPins pins) := by
    rw [inputPins, otherPins, Finset.disjoint_filter]
    intro p _ h1 h2
    rcases hp : pins p with ⟨i, ng⟩ | ⟨pat, hpat, ng⟩ | ⟨b⟩ <;>
      simp [hp, Read.inputIdx, Read.otherPat] at h1 h2
  rw [← Finset.card_union_of_disjoint hdisj]
  exact (Finset.card_le_univ _).trans (by simp)

theorem lemma2 (hnK : K < n) (q : Fin n → Bool) (pins : Fin K → Read n q)
    (table : (Fin K → Bool) → Bool) (b : Bool) :
    (fun x => Bool.xor b (table fun p => (pins p).eval x)) ≠ minterm q := by
  classical
  have h0 : 0 < n := by omega
  -- R: the inputs read by input pins; P: the patterns read through other outputs
  let R : Finset (Fin n) := (inputPins pins).image fun p => ((pins p).inputIdx).getD ⟨0, h0⟩
  let P : Finset (Fin n → Bool) := (otherPins pins).image fun p => ((pins p).otherPat).getD q
  have hR : R.card ≤ (inputPins pins).card := card_image_le
  have hP : P.card ≤ (otherPins pins).card := card_image_le
  have hsplit := pins_card pins
  -- U: the unread inputs
  let U : Finset (Fin n) := univ.filter fun i => i ∉ R
  have hRU : R.card + U.card = n := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n))) (fun i => i ∈ R)
    rw [card_univ, Fintype.card_fin] at h
    have hfR : (univ.filter fun i => i ∈ R) = R := by ext i; simp
    rw [hfR] at h
    exact h
  -- C: the patterns obtained by flipping q at one unread input
  let C : Finset (Fin n → Bool) := U.image (flip q)
  have hC : C.card = U.card := card_image_of_injective _ (flip_injective q)
  have hlt : P.card < C.card := by omega
  obtain ⟨x, hxC, hxP⟩ := exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨i, hiU, rfl⟩ := mem_image.mp hxC
  have hiR : i ∉ R := (mem_filter.mp hiU).2
  -- every pin reads the same value at `flip q i` and at `q`
  have hpins : ∀ p, (pins p).eval (flip q i) = (pins p).eval q := by
    intro p
    rcases hp : pins p with ⟨r, ng⟩ | ⟨pat, hpat, ng⟩ | ⟨c⟩
    · have hr : r ≠ i := by
        rintro rfl
        apply hiR
        refine mem_image.mpr ⟨p, ?_, ?_⟩
        · rw [inputPins, mem_filter]
          exact ⟨mem_univ _, by rw [hp]; rfl⟩
        · rw [hp]
          rfl
      simp [Read.eval, flip_apply_of_ne q hr]
    · have hne : flip q i ≠ pat := by
        intro h
        apply hxP
        refine mem_image.mpr ⟨p, ?_, ?_⟩
        · rw [otherPins, mem_filter]
          exact ⟨mem_univ _, by rw [hp]; rfl⟩
        · rw [hp]
          exact h.symm
      have hne' : q ≠ pat := fun h => hpat h.symm
      simp [Read.eval, minterm, hne, hne']
    · rfl
  intro h
  have h1 : Bool.xor b (table fun p => (pins p).eval (flip q i)) = minterm q (flip q i) :=
    congrFun h (flip q i)
  have h2 : Bool.xor b (table fun p => (pins p).eval q) = minterm q q := congrFun h q
  rw [show (fun p => (pins p).eval (flip q i)) = (fun p => (pins p).eval q) from funext hpins] at h1
  rw [h1] at h2
  simp [minterm, flip_ne q i] at h2

end DecoderOptimality
