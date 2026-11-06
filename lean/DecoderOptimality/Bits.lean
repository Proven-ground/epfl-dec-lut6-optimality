import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-!
# Six-bit points

The 64 points of the reduced question are the natural numbers below 64; bit `k` of point `z` is
`z.testBit k`. `ofBits` builds a point from its bits.
-/

namespace DecoderOptimality

/-- The number whose bits, least significant first, are the list. -/
def ofBits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * ofBits bs

theorem ofBits_cons (b : Bool) (bs : List Bool) :
    ofBits (b :: bs) = (if b then 1 else 0) + 2 * ofBits bs := rfl

theorem ofBits_cons_le (b : Bool) (bs : List Bool) : ofBits (b :: bs) ≤ 1 + 2 * ofBits bs := by
  rw [ofBits_cons]
  cases b <;> simp

theorem ofBits_lt (bs : List Bool) : ofBits bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp [ofBits]
  | cons b bs ih =>
    have h := ofBits_cons_le b bs
    rw [List.length_cons, Nat.pow_succ]
    omega

theorem ofBits_cons_mod (b : Bool) (bs : List Bool) : ofBits (b :: bs) % 2 = if b then 1 else 0 := by
  rw [ofBits_cons]
  cases b <;> simp <;> omega

theorem ofBits_cons_div (b : Bool) (bs : List Bool) : ofBits (b :: bs) / 2 = ofBits bs := by
  rw [ofBits_cons]
  cases b <;> simp <;> omega

theorem testBit_ofBits (bs : List Bool) : ∀ k, (ofBits bs).testBit k = bs.getD k false := by
  induction bs with
  | nil => intro k; simp [ofBits, Nat.zero_testBit]
  | cons b bs ih =>
    intro k
    cases k with
    | zero =>
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_zero, Nat.div_one, ofBits_cons_mod]
      cases b <;> simp [List.getD]
    | succ k =>
      rw [Nat.testBit_eq_decide_div_mod_eq, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2,
        ← Nat.div_div_eq_div_mul, ofBits_cons_div, ← Nat.testBit_eq_decide_div_mod_eq, ih]
      simp [List.getD]

/-- The point with the given six bits. -/
def ofBits6 (f : Fin 6 → Bool) : Nat :=
  ofBits [f 0, f 1, f 2, f 3, f 4, f 5]

theorem ofBits6_lt (f : Fin 6 → Bool) : ofBits6 f < 64 := by
  have := ofBits_lt [f 0, f 1, f 2, f 3, f 4, f 5]
  simpa [ofBits6] using this

theorem testBit_ofBits6 (f : Fin 6 → Bool) (k : Fin 6) : (ofBits6 f).testBit k = f k := by
  unfold ofBits6
  rw [testBit_ofBits]
  fin_cases k <;> rfl

/-- Two points below 64 with the same six bits are equal. -/
theorem eq_of_testBit_eq_six {z z' : Nat} (hz : z < 64) (hz' : z' < 64)
    (h : ∀ k : Fin 6, z.testBit k = z'.testBit k) : z = z' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · exact h ⟨i, hi⟩
  · have h64 : (64 : Nat) ≤ 2 ^ i := by
      calc (64 : Nat) = 2 ^ 6 := by decide
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

theorem xor_lt_64 {z s : Nat} (hz : z < 64) (hs : s < 64) : z ^^^ s < 64 :=
  Nat.xor_lt_two_pow (n := 6) hz hs

theorem xor_ne_self_of_ne_zero {z s : Nat} (hs : s ≠ 0) : z ^^^ s ≠ z := by
  intro h
  apply hs
  have this : z ^^^ (z ^^^ s) = z ^^^ z := congrArg (fun t => z ^^^ t) h
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at this
  exact this

theorem xor_left_injective_nat (z : Nat) : Function.Injective (fun s : Nat => z ^^^ s) := by
  intro s s' h
  have this : z ^^^ (z ^^^ s) = z ^^^ (z ^^^ s') := congrArg (fun t => z ^^^ t) h
  rw [← Nat.xor_assoc, ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.zero_xor] at this
  exact this

end DecoderOptimality
