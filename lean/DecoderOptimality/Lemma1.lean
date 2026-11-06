import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Find
import DecoderOptimality.Model

/-!
# Lemma 1 of the paper: one LUT per output

Every pattern's minterm is computed by some node (`computesDecoder`); `out q` is the first such node.
Distinct minterms are distinct functions, and a minterm is never the complement of a minterm, so `out`
is injective and the network has at least `2 ^ n` nodes.
-/

namespace DecoderOptimality

open Classical

variable {n K : Nat} (net : Network n K)

/-- A node computing two minterms (each up to a free inverter) computes one minterm. -/
theorem Network.signed_eq_iff (hn : 2 ≤ n) {j : Nat} {b b' : Bool} {q q' : Fin n → Bool}
    (h : net.signed j b = minterm q) (h' : net.signed j b' = minterm q') : q = q' := by
  by_cases hb : b = b'
  · subst hb
    exact minterm_injective (h.symm.trans h')
  · exfalso
    have hb' : b' = !b := by cases b <;> cases b' <;> simp_all
    apply minterm_ne_not hn q' q
    funext x
    have e1 := congrFun h x
    have e2 := congrFun h' x
    simp only [Network.signed] at e1 e2
    rw [← e2, ← e1, hb']
    cases b <;> cases net.nodeFun j x <;> rfl

variable (hdec : net.computesDecoder)

/-- The first node computing the minterm of `q`, up to a free inverter. -/
noncomputable def out (q : Fin n → Bool) : Nat :=
  Nat.find (hdec q)

theorem out_lt (q : Fin n → Bool) : out net hdec q < net.nodes.size :=
  (Nat.find_spec (hdec q)).1

theorem out_spec (q : Fin n → Bool) : ∃ b : Bool, net.signed (out net hdec q) b = minterm q :=
  (Nat.find_spec (hdec q)).2

theorem out_min {q : Fin n → Bool} {j : Nat} (hj : j < out net hdec q) :
    ¬ (j < net.nodes.size ∧ ∃ b : Bool, net.signed j b = minterm q) :=
  Nat.find_min (hdec q) hj

theorem out_le {q : Fin n → Bool} {j : Nat}
    (h : j < net.nodes.size ∧ ∃ b : Bool, net.signed j b = minterm q) : out net hdec q ≤ j :=
  Nat.find_min' (hdec q) h

theorem out_injective (hn : 2 ≤ n) : Function.Injective (out net hdec) := by
  intro q q' h
  obtain ⟨b, hb⟩ := out_spec net hdec q
  obtain ⟨b', hb'⟩ := out_spec net hdec q'
  rw [h] at hb
  exact net.signed_eq_iff hn hb hb'

include hdec in
/-- Lemma 1: at least one node per pattern. -/
theorem card_le_size (hn : 2 ≤ n) : Fintype.card (Fin n → Bool) ≤ net.nodes.size := by
  have := Fintype.card_le_of_injective
    (fun q : Fin n → Bool => (⟨out net hdec q, out_lt net hdec q⟩ : Fin net.nodes.size))
    (fun q q' h => out_injective net hdec hn (by simpa [Fin.ext_iff] using h))
  simpa using this

include hdec in
theorem two_pow_le_size (hn : 2 ≤ n) : 2 ^ n ≤ net.nodes.size := by
  have := card_le_size net hdec hn
  rwa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at this

end DecoderOptimality
