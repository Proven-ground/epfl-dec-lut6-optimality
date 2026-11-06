import DecoderOptimality.Encoder
import DecoderOptimality.Counter
import DecoderOptimality.Bits

/-!
# A satisfying assignment of the formula from the 64-point data

`Data` holds a shared function `Y`, a build order `out`, the pattern `q z` of every point and the free
set `mz z` chosen for it. `Facts` are the five properties of that data which the reduction delivers. From
them, `assign` satisfies every clause of `Bound.cnf`.
-/

namespace DecoderOptimality.Bound

open Std.Sat

/-- The data an assignment is built from. -/
structure Data where
  Y : (Fin 8 → Bool) → Bool
  out : (Fin 8 → Bool) → Nat
  /-- The pattern of point `z`: its bits on the six inputs of `Y`, zero elsewhere. -/
  q : Nat → (Fin 8 → Bool)
  /-- The free set chosen for point `z`, as a mask. -/
  mz : Nat → Nat

namespace Data

variable (d : Data)

/-- `Y` at point `z`, complemented so that `yv 0 = false`. -/
def yv (z : Nat) : Bool := Bool.xor (d.Y (d.q 0)) (d.Y (d.q z))
def pv (a b : Nat) : Bool := decide (d.out (d.q a) < d.out (d.q b))
def cv (z m : Nat) : Bool := decide (m = d.mz z)
def gv (z m s : Nat) : Bool := d.cv z m && (d.yv z == d.yv (z ^^^ s))
/-- The counted literal values of option `(z, m)`. -/
def vals (z m : Nat) (s : Nat) : Bool := if member m s then d.gv z m s else false
def sv (z m i j : Nat) : Bool := decide (j + 1 ≤ cnt (d.vals z m) i)

/-- The assignment, by decoding the atom blocks. -/
def assign (n : Nat) : Bool :=
  if n < 64 then d.yv n
  else if n < 4160 then d.pv ((n - 64) / 64) ((n - 64) % 64)
  else if n < 8256 then d.cv ((n - 4160) / 64) ((n - 4160) % 64)
  else if n < 270400 then d.gv ((n - 8256) / 4096) ((n - 8256) / 64 % 64) ((n - 8256) % 64)
  else if n < 1318976 then
    d.sv ((n - 270400) / 16384) ((n - 270400) / 256 % 64) ((n - 270400) / 4 % 64) ((n - 270400) % 4)
  else false

theorem assign_y {z : Nat} (hz : z < 64) : d.assign (yA z) = d.yv z := by
  unfold assign yA
  rw [if_pos hz]

theorem assign_p {a b : Nat} (ha : a < 64) (hb : b < 64) : d.assign (pA a b) = d.pv a b := by
  unfold assign pA
  rw [if_neg (by omega), if_pos (by omega)]
  have h1 : (64 + 64 * a + b - 64) / 64 = a := by omega
  have h2 : (64 + 64 * a + b - 64) % 64 = b := by omega
  rw [h1, h2]

theorem assign_c {z m : Nat} (hz : z < 64) (hm : m < 64) : d.assign (cA z m) = d.cv z m := by
  unfold assign cA
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have h1 : (4160 + 64 * z + m - 4160) / 64 = z := by omega
  have h2 : (4160 + 64 * z + m - 4160) % 64 = m := by omega
  rw [h1, h2]

theorem assign_g {z m s : Nat} (hz : z < 64) (hm : m < 64) (hs : s < 64) :
    d.assign (gA z m s) = d.gv z m s := by
  unfold assign gA
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have h1 : (8256 + 4096 * z + 64 * m + s - 8256) / 4096 = z := by omega
  have h2 : (8256 + 4096 * z + 64 * m + s - 8256) / 64 % 64 = m := by omega
  have h3 : (8256 + 4096 * z + 64 * m + s - 8256) % 64 = s := by omega
  rw [h1, h2, h3]

theorem assign_s {z m i j : Nat} (hz : z < 64) (hm : m < 64) (hi : i < 64) (hj : j < 4) :
    d.assign (sA z m i j) = d.sv z m i j := by
  unfold assign sA
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have h1 : (270400 + 16384 * z + 256 * m + 4 * i + j - 270400) / 16384 = z := by omega
  have h2 : (270400 + 16384 * z + 256 * m + 4 * i + j - 270400) / 256 % 64 = m := by omega
  have h3 : (270400 + 16384 * z + 256 * m + 4 * i + j - 270400) / 4 % 64 = i := by omega
  have h4 : (270400 + 16384 * z + 256 * m + 4 * i + j - 270400) % 4 = j := by omega
  rw [h1, h2, h3, h4]

theorem assign_false : d.assign falseA = false := by
  unfold assign falseA
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem flipLit_true (a : Nat → Bool) (l : Lit) :
    (a (flipLit l).1 = (flipLit l).2) ↔ ¬ (a l.1 = l.2) := by
  simp only [flipLit]
  cases h1 : a l.1 <;> cases h2 : l.2 <;> simp

theorem eval_cl_any (a : Nat → Bool) (l : List Lit) :
    (cl l).eval a = l.any fun x => a x.1 == x.2 := by
  unfold cl
  rw [eval_foldl, CNF.Clause.eval_empty, Bool.false_or]

/-- The precedence literal of two distinct points holds exactly when the first is built first. -/
theorem prec_true {a b : Nat} (ha : a < 64) (hb : b < 64) (hab : a ≠ b)
    (hinj : d.out (d.q a) ≠ d.out (d.q b)) :
    (d.assign (prec a b).1 = (prec a b).2) ↔ d.out (d.q a) < d.out (d.q b) := by
  unfold prec
  split
  · simp only [pos]
    rw [d.assign_p ha hb]
    simp [pv]
  · simp only [neg]
    rw [d.assign_p hb ha]
    simp only [pv, decide_eq_false_iff_not]
    constructor <;> intro h <;> omega

end Data

/-- What the reduction delivers about the data. -/
structure Facts (d : Data) : Prop where
  inj : ∀ a b, a < 64 → b < 64 → a ≠ b → d.out (d.q a) ≠ d.out (d.q b)
  mz_lt : ∀ z, z < 64 → d.mz z < 64
  mz_valid : ∀ z, z < 64 → valid (d.mz z) = true
  prec_of_eq : ∀ z s, z < 64 → s < 64 → member (d.mz z) s = true →
    d.Y (d.q (z ^^^ s)) = d.Y (d.q z) → d.out (d.q (z ^^^ s)) < d.out (d.q z)
  count : ∀ z, z < 64 →
    ((Finset.range 64).filter fun s =>
      member (d.mz z) s = true ∧ d.Y (d.q (z ^^^ s)) = d.Y (d.q z)).card ≤ bound (d.mz z)

theorem memberClauses_sat (d : Data) (hf : Facts d) {z m s : Nat} (hz : z < 64) (hm : m < 64)
    (hs : s < 64) (hmem : member m s = true) : ∀ c ∈ memberClauses z m s, c.eval d.assign = true := by
  intro c hc
  have hx : z ^^^ s < 64 := xor_lt_64 hz hs
  have hs0 : s ≠ 0 := by
    unfold member at hmem
    rw [Bool.and_eq_true, bne_iff_ne] at hmem
    exact hmem.1
  have hxz : z ^^^ s ≠ z := xor_ne_self_of_ne_zero hs0
  have hC := d.assign_c hz hm
  have hYz := d.assign_y hz
  have hYx := d.assign_y hx
  have hG := d.assign_g hz hm hs
  -- for the chosen option, a member on which Y agrees precedes z
  have hprec : m = d.mz z → d.yv z = d.yv (z ^^^ s) →
      (d.assign (prec (z ^^^ s) z).1 == (prec (z ^^^ s) z).2) = true := by
    intro hmz heq
    have hYeq : d.Y (d.q (z ^^^ s)) = d.Y (d.q z) := by
      unfold Data.yv at heq
      exact (Bool.xor_right_inj.mp heq).symm
    have hlt := hf.prec_of_eq z s hz hs (hmz ▸ hmem) hYeq
    have := (d.prec_true hx hz hxz (hf.inj _ _ hx hz hxz)).mpr hlt
    simpa using this
  simp only [memberClauses, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rw [Data.eval_cl_any] <;>
    simp only [List.any_cons, List.any_nil, pos, neg, hC, hYz, hYx, hG, Bool.or_false, Data.gv]
  · by_cases hmz : m = d.mz z
    · have hcv : d.cv z m = true := by simp [Data.cv, hmz]
      by_cases heq : d.yv z = d.yv (z ^^^ s)
      · rw [hprec hmz heq]
        simp
      · rw [hcv]
        cases h1 : d.yv z <;> cases h2 : d.yv (z ^^^ s) <;> simp_all
    · have hcv : d.cv z m = false := by simp [Data.cv, hmz]
      rw [hcv]
      simp
  · by_cases hmz : m = d.mz z
    · have hcv : d.cv z m = true := by simp [Data.cv, hmz]
      by_cases heq : d.yv z = d.yv (z ^^^ s)
      · rw [hprec hmz heq]
        simp
      · rw [hcv]
        cases h1 : d.yv z <;> cases h2 : d.yv (z ^^^ s) <;> simp_all
    · have hcv : d.cv z m = false := by simp [Data.cv, hmz]
      rw [hcv]
      simp
  · cases hc1 : d.cv z m <;> cases h1 : d.yv z <;> cases h2 : d.yv (z ^^^ s) <;> simp
  · cases hc1 : d.cv z m <;> cases h1 : d.yv z <;> cases h2 : d.yv (z ^^^ s) <;> simp
  · cases hc1 : d.cv z m <;> cases h1 : d.yv z <;> cases h2 : d.yv (z ^^^ s) <;> simp
  · cases hc1 : d.cv z m <;> cases h1 : d.yv z <;> cases h2 : d.yv (z ^^^ s) <;> simp
  · cases hc1 : d.cv z m <;> cases h1 : d.yv z <;> cases h2 : d.yv (z ^^^ s) <;> simp

theorem atMost_sat (d : Data) (hf : Facts d) {z m : Nat} (hz : z < 64) (hm : m < 64) :
    ∀ c ∈ atMostClauses z m, c.eval d.assign = true := by
  intro c hc
  -- the counted literal of each position has the value `vals`
  have hlit : ∀ i, i < 64 →
      (d.assign (guardLit z m i).1 = (guardLit z m i).2 ↔ d.vals z m i = true) := by
    intro i hi
    unfold guardLit Data.vals
    by_cases hmem : member m i = true
    · rw [if_pos hmem, if_pos hmem]
      simp only [pos]
      rw [d.assign_g hz hm hi]
    · rw [if_neg hmem, if_neg hmem]
      simp only [pos]
      rw [d.assign_false]
  -- every prefix count is within the bound
  have htot : ∀ i, i < 64 → cnt (d.vals z m) i ≤ bound m := by
    intro i hi
    have h63 : cnt (d.vals z m) i ≤ cnt (d.vals z m) 63 := cnt_mono _ (by omega)
    refine h63.trans ?_
    show ((Finset.range 64).filter fun t => d.vals z m t = true).card ≤ bound m
    by_cases hmz : m = d.mz z
    · subst hmz
      have hcount := hf.count z hz
      refine le_trans (le_of_eq ?_) hcount
      congr 1
      apply Finset.filter_congr
      intro t _
      unfold Data.vals Data.gv Data.cv Data.yv
      have hdec : decide (d.mz z = d.mz z) = true := by simp
      rw [hdec, Bool.true_and]
      by_cases hmem : member (d.mz z) t = true
      · rw [if_pos hmem, beq_iff_eq, Bool.xor_right_inj]
        constructor
        · intro h
          exact ⟨hmem, h.symm⟩
        · rintro ⟨-, h⟩
          exact h.symm
      · rw [if_neg hmem]
        simp [hmem]
    · have hnone : ∀ t ∈ Finset.range 64, ¬ (d.vals z m t = true) := by
        intro t _ h
        unfold Data.vals Data.gv Data.cv at h
        split at h
        · simp [hmz] at h
        · cases h
      rw [Finset.filter_false_of_mem hnone, Finset.card_empty]
      exact Nat.zero_le _
  unfold atMostClauses at hc
  split at hc
  · rename_i hb0
    rw [List.mem_map] at hc
    obtain ⟨s, hs, rfl⟩ := hc
    rw [List.mem_range] at hs
    rw [eval_cl_iff]
    refine ⟨flipLit (guardLit z m s), by simp, ?_⟩
    rw [Data.flipLit_true, hlit s hs]
    intro hv
    have h1 := htot s hs
    rw [hb0] at h1
    have h2 := one_le_cnt (d.vals z m) s hv
    omega
  · rename_i hb0
    exact counter_sat 64 (bound m) (Nat.pos_of_ne_zero hb0) (guardLit z m) (sA z m) d.assign
      (d.vals z m) hlit
      (fun i j hi hj => by rw [d.assign_s hz hm hi (by have := bound_le m; omega)]; rfl)
      htot c hc

/-- The formula is satisfied by the assignment built from data with the five facts. -/
theorem sat (d : Data) (hf : Facts d) : CNF.Sat d.assign cnf := by
  rw [sat_iff]
  intro c hc
  unfold clauses at hc
  rw [List.mem_append, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · -- the two unit clauses
    simp only [unitClauses, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rw [eval_cl_iff]
      refine ⟨neg (yA 0), by simp, ?_⟩
      simp only [neg]
      rw [d.assign_y (by omega)]
      simp [Data.yv]
    · rw [eval_cl_iff]
      refine ⟨neg falseA, by simp, ?_⟩
      simp only [neg]
      exact d.assign_false
  · -- transitivity of the build order
    unfold transClauses at hc
    rw [List.mem_flatMap] at hc
    obtain ⟨a, ha, hc⟩ := hc
    rw [List.mem_flatMap] at hc
    obtain ⟨b, hb, hc⟩ := hc
    rw [List.mem_filterMap] at hc
    obtain ⟨c', hc', hcc⟩ := hc
    rw [List.mem_range] at ha hb hc'
    split at hcc
    · rename_i hne
      cases hcc
      obtain ⟨hab, hbc, hac⟩ := hne
      rw [eval_cl_iff]
      by_cases h1 : d.out (d.q a) < d.out (d.q b)
      · by_cases h2 : d.out (d.q b) < d.out (d.q c')
        · refine ⟨prec a c', by simp, ?_⟩
          exact (d.prec_true ha hc' hac (hf.inj a c' ha hc' hac)).mpr (lt_trans h1 h2)
        · refine ⟨flipLit (prec b c'), by simp, ?_⟩
          rw [Data.flipLit_true, d.prec_true hb hc' hbc (hf.inj b c' hb hc' hbc)]
          exact h2
      · refine ⟨flipLit (prec a b), by simp, ?_⟩
        rw [Data.flipLit_true, d.prec_true ha hb hab (hf.inj a b ha hb hab)]
        exact h1
    · cases hcc
  · -- the clauses of a point
    rw [List.mem_flatMap] at hc
    obtain ⟨z, hz, hc⟩ := hc
    rw [List.mem_range] at hz
    unfold pointClauses at hc
    rw [List.mem_cons] at hc
    rcases hc with rfl | hc
    · unfold optionClause
      rw [eval_cl_iff]
      refine ⟨pos (cA z (d.mz z)), ?_, ?_⟩
      · rw [List.mem_filterMap]
        exact ⟨d.mz z, List.mem_range.mpr (hf.mz_lt z hz), by rw [if_pos (hf.mz_valid z hz)]⟩
      · simp only [pos]
        rw [d.assign_c hz (hf.mz_lt z hz)]
        simp [Data.cv]
    · rw [List.mem_flatMap] at hc
      obtain ⟨m, hm, hc⟩ := hc
      rw [List.mem_range] at hm
      unfold optionClauses at hc
      split at hc
      · rw [List.mem_append] at hc
        rcases hc with hc | hc
        · rw [List.mem_flatMap] at hc
          obtain ⟨s, hs, hc⟩ := hc
          rw [mem_members] at hs
          exact memberClauses_sat d hf hz hm hs.1 hs.2 c hc
        · exact atMost_sat d hf hz hm c hc
      · simp at hc

end DecoderOptimality.Bound
