import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import DecoderOptimality.Encoder

/-!
# Sinz's sequential counter is satisfied by the running count

For literal values `vals 0, …, vals (L-1)` with every prefix count at most `k`, the assignment that sets
register `(i, j)` to "at least `j + 1` of the first `i + 1` literals hold" satisfies every counter clause.
-/

namespace DecoderOptimality.Bound

open Finset

/-- The number of `t ≤ i` with `vals t = true`. -/
def cnt (vals : Nat → Bool) (i : Nat) : Nat :=
  ((range (i + 1)).filter fun t => vals t = true).card

theorem cnt_zero (vals : Nat → Bool) : cnt vals 0 = if vals 0 then 1 else 0 := by
  unfold cnt
  rw [range_one, filter_singleton]
  by_cases h : vals 0 = true
  · rw [if_pos h, if_pos h, card_singleton]
  · rw [if_neg h, if_neg h, card_empty]

theorem cnt_succ (vals : Nat → Bool) (i : Nat) :
    cnt vals (i + 1) = cnt vals i + if vals (i + 1) then 1 else 0 := by
  unfold cnt
  rw [range_add_one, filter_insert]
  by_cases h : vals (i + 1) = true
  · rw [if_pos h, if_pos h, card_insert_of_notMem (by simp)]
  · simp [h]

theorem cnt_mono (vals : Nat → Bool) : ∀ {i i' : Nat}, i ≤ i' → cnt vals i ≤ cnt vals i' := by
  intro i i' h
  induction i' with
  | zero =>
    have : i = 0 := by omega
    subst this
    exact le_rfl
  | succ i' ih =>
    rcases Nat.lt_or_ge i (i' + 1) with hlt | hge
    · have := ih (by omega)
      rw [cnt_succ]
      split <;> omega
    · have : i = i' + 1 := by omega
      subst this
      exact le_rfl

theorem one_le_cnt (vals : Nat → Bool) (i : Nat) (h : vals i = true) : 1 ≤ cnt vals i := by
  cases i with
  | zero => simp [cnt_zero, h]
  | succ i => rw [cnt_succ, if_pos h]; omega

theorem bool_eq_not_of_ne {x y : Bool} (h : x ≠ y) : x = !y := by
  cases x <;> cases y <;> simp_all

theorem counter_sat (L k : Nat) (hk : 0 < k) (lit : Nat → Lit) (reg : Nat → Nat → Nat) (a : Nat → Bool)
    (vals : Nat → Bool)
    (hlit : ∀ i, i < L → (a (lit i).1 = (lit i).2 ↔ vals i = true))
    (hreg : ∀ i j, i < L → j < k → a (reg i j) = decide (j + 1 ≤ cnt vals i))
    (htot : ∀ i, i < L → cnt vals i ≤ k) :
    ∀ c ∈ counterClauses L k lit reg, c.eval a = true := by
  intro c hc
  unfold counterClauses at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨i, hi, hc⟩ := hc
  rw [List.mem_range] at hi
  rw [List.mem_cons] at hc
  rcases hc with rfl | hc
  · -- the literal implies the first register
    rw [eval_cl_iff]
    by_cases hv : vals i = true
    · refine ⟨pos (reg i 0), by simp, ?_⟩
      simp only [pos]
      rw [hreg i 0 hi hk]
      simp [one_le_cnt vals i hv]
    · refine ⟨flipLit (lit i), by simp, ?_⟩
      simp only [flipLit]
      exact bool_eq_not_of_ne fun h => hv ((hlit i hi).mp h)
  · split at hc
    · simp at hc
    · rename_i hi0
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel] at hc
      rw [List.mem_append, List.mem_append] at hc
      rcases hc with (hc | hc) | hc
      · -- registers are monotone along the chain
        rw [List.mem_map] at hc
        obtain ⟨j, hj, rfl⟩ := hc
        rw [List.mem_range] at hj
        rw [eval_cl_iff]
        by_cases hr : a (reg i' j) = true
        · refine ⟨pos (reg (i' + 1) j), by simp, ?_⟩
          simp only [pos]
          rw [hreg _ _ hi hj]
          rw [hreg _ _ (by omega) hj] at hr
          simp at hr ⊢
          exact hr.trans (cnt_mono vals (Nat.le_succ i'))
        · refine ⟨neg (reg i' j), by simp, ?_⟩
          simp only [neg]
          simpa using hr
      · -- a true literal advances the count
        rw [List.mem_filterMap] at hc
        obtain ⟨j, hj, hcj⟩ := hc
        rw [List.mem_range] at hj
        split at hcj
        · cases hcj
        · rename_i hj0
          cases hcj
          rw [eval_cl_iff]
          by_cases hv : vals (i' + 1) = true
          · by_cases hr : a (reg i' (j - 1)) = true
            · refine ⟨pos (reg (i' + 1) j), by simp, ?_⟩
              simp only [pos]
              rw [hreg _ _ hi hj]
              rw [hreg _ _ (by omega) (by omega)] at hr
              simp at hr ⊢
              rw [cnt_succ, if_pos hv]
              omega
            · refine ⟨neg (reg i' (j - 1)), by simp, ?_⟩
              simp only [neg]
              simpa using hr
          · refine ⟨flipLit (lit (i' + 1)), by simp, ?_⟩
            simp only [flipLit]
            exact bool_eq_not_of_ne fun h => hv ((hlit (i' + 1) hi).mp h)
      · -- a true literal cannot follow a full counter
        rw [List.mem_singleton] at hc
        subst hc
        rw [eval_cl_iff]
        by_cases hv : vals (i' + 1) = true
        · refine ⟨neg (reg i' (k - 1)), by simp, ?_⟩
          simp only [neg]
          rw [hreg _ _ (by omega) (by omega)]
          have h1 := htot (i' + 1) hi
          rw [cnt_succ, if_pos hv] at h1
          simp
          omega
        · refine ⟨flipLit (lit (i' + 1)), by simp, ?_⟩
          simp only [flipLit]
          exact bool_eq_not_of_ne fun h => hv ((hlit (i' + 1) hi).mp h)

end DecoderOptimality.Bound
