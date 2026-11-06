import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import DecoderOptimality.Model

/-!
# The object the lower bound reduces to

After Lemmas 1 and 2, a network of `2 ^ n + 1` LUTs has one non-output node `Y`, reading a set `V` of at
most `K` inputs, and a build order `out` on the patterns. For an output `q` reading `u` other outputs and
leaving the inputs `F` unread, the class `cls Y q F` is the set of patterns `x ≠ q` that agree with `q`
outside `F` and have `Y x = Y q`. The output can be the minterm of `q` only when the class has at most `u`
members, all built before `q` (`Admissible`), and `|F| ≥ n - K + 1 + u`.

`Reduced` records exactly these facts; `Structure.lean` derives it from a network and
`Dominance.lean` and `Bridge.lean` consume it.
-/

namespace DecoderOptimality

open Finset

variable {n : Nat}

/-- The class of `q` for free inputs `F` under the shared function `Y`. -/
def cls (Y : (Fin n → Bool) → Bool) (q : Fin n → Bool) (F : Finset (Fin n)) : Finset (Fin n → Bool) :=
  univ.filter fun x => x ≠ q ∧ (∀ i, i ∉ F → x i = q i) ∧ Y x = Y q

theorem mem_cls {Y : (Fin n → Bool) → Bool} {q x : Fin n → Bool} {F : Finset (Fin n)} :
    x ∈ cls Y q F ↔ x ≠ q ∧ (∀ i, i ∉ F → x i = q i) ∧ Y x = Y q := by
  simp [cls]

/-- `(F, u)` is admissible for `q`: at most `u` class members, all built before `q`. -/
def Admissible (Y : (Fin n → Bool) → Bool) (out : (Fin n → Bool) → Nat) (q : Fin n → Bool)
    (F : Finset (Fin n)) (u : Nat) : Prop :=
  (cls Y q F).card ≤ u ∧ ∀ x ∈ cls Y q F, out x < out q

theorem cls_mono {Y : (Fin n → Bool) → Bool} {q : Fin n → Bool} {F F' : Finset (Fin n)} (h : F' ⊆ F) :
    cls Y q F' ⊆ cls Y q F := by
  intro x hx
  rw [mem_cls] at hx ⊢
  refine ⟨hx.1, fun i hi => hx.2.1 i (fun h' => hi (h h')), hx.2.2⟩

theorem Admissible.mono {Y : (Fin n → Bool) → Bool} {out : (Fin n → Bool) → Nat} {q : Fin n → Bool}
    {F F' : Finset (Fin n)} {u : Nat} (h : F' ⊆ F) (hadm : Admissible Y out q F u) :
    Admissible Y out q F' u :=
  ⟨(card_le_card (cls_mono h)).trans hadm.1, fun x hx => hadm.2 x (cls_mono h hx)⟩

/-- What Lemmas 1 and 2 leave of a network of `2 ^ n + 1` LUTs of `K` inputs. -/
structure Reduced (n K : Nat) where
  /-- The function of the one non-output node. -/
  Y : (Fin n → Bool) → Bool
  /-- The inputs it reads. -/
  V : Finset (Fin n)
  card_V : V.card ≤ K
  ignores : ∀ x x' : Fin n → Bool, (∀ i ∈ V, x i = x' i) → Y x = Y x'
  /-- The build order of the outputs. -/
  out : (Fin n → Bool) → Nat
  out_injective : Function.Injective out
  /-- Every output has an admissible pair with enough free inputs. -/
  admissible : ∀ q, ∃ (F : Finset (Fin n)) (u : Nat), n - K + 1 + u ≤ F.card ∧ Admissible Y out q F u

end DecoderOptimality
