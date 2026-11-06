import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Choose
import DecoderOptimality.Dominance
import DecoderOptimality.Assignment

/-!
# From the reduced object to a satisfying assignment

Pad `V` to six inputs `V'`, enumerate them by `emb : Fin 6 ↪o Fin 8`, and read every point `z < 64` as the
pattern `q z` whose value on `emb k` is bit `k` of `z` and which is zero outside `V'`. Lemma 3 gives every
`q z` an admissible free set `F z ⊆ V` with `|F z| = 3 + u z`; its mask is `mz z`. The five facts of
`Assignment.lean` follow, so the formula is satisfiable.
-/

namespace DecoderOptimality

open Finset

theorem bridge (red : Reduced 8 6) : ∃ a, Std.Sat.CNF.Sat a Bound.cnf := by
  classical
  -- pad V to six inputs
  obtain ⟨V', hVV', -, hV'⟩ := exists_subsuperset_card_eq (subset_univ red.V) red.card_V
    (by simp : 6 ≤ (univ : Finset (Fin 8)).card)
  obtain ⟨emb, hemb⟩ : ∃ emb : Fin 6 ↪o Fin 8, emb = V'.orderEmbOfFin hV' := ⟨_, rfl⟩
  have hemb_mem : ∀ k, emb k ∈ V' := by
    intro k
    rw [hemb]
    exact orderEmbOfFin_mem V' hV' k
  have hemb_inj : Function.Injective emb := emb.injective
  have hsurj : ∀ i ∈ V', ∃ k, emb k = i := by
    intro i hi
    have hr := range_orderEmbOfFin V' hV'
    rw [← hemb] at hr
    have : i ∈ Set.range emb := by rw [hr]; exact hi
    exact Set.mem_range.mp this
  -- the pattern of a point: its bits on V', zero elsewhere
  obtain ⟨idx, hidx⟩ : ∃ idx : ∀ i, i ∈ V' → Fin 6, ∀ i (hi : i ∈ V'), emb (idx i hi) = i :=
    ⟨fun i hi => Classical.choose (hsurj i hi), fun i hi => Classical.choose_spec (hsurj i hi)⟩
  obtain ⟨embed, hembed⟩ : ∃ embed : (Fin 6 → Bool) → (Fin 8 → Bool),
      ∀ f i, embed f i = if hi : i ∈ V' then f (idx i hi) else false :=
    ⟨fun f i => if hi : i ∈ V' then f (idx i hi) else false, fun _ _ => rfl⟩
  have embed_emb : ∀ f k, embed f (emb k) = f k := by
    intro f k
    rw [hembed, dif_pos (hemb_mem k)]
    exact congrArg f (hemb_inj (hidx (emb k) (hemb_mem k)))
  have embed_out : ∀ f i, i ∉ V' → embed f i = false := by
    intro f i hi
    rw [hembed, dif_neg hi]
  have embed_inj : Function.Injective embed := by
    intro f f' h
    funext k
    rw [← embed_emb f k, ← embed_emb f' k, h]
  obtain ⟨q, hq⟩ : ∃ q : Nat → (Fin 8 → Bool), ∀ z, q z = embed fun k => z.testBit k :=
    ⟨_, fun _ => rfl⟩
  have hq_emb : ∀ z k, q z (emb k) = z.testBit k := by
    intro z k
    rw [hq, embed_emb]
  have hq_out : ∀ z i, i ∉ V' → q z i = false := by
    intro z i hi
    rw [hq, embed_out _ _ hi]
  have hq_inj : ∀ z z', z < 64 → z' < 64 → q z = q z' → z = z' := by
    intro z z' hz hz' h
    rw [hq, hq] at h
    have := embed_inj h
    exact eq_of_testBit_eq_six hz hz' fun k => congrFun this k
  -- the admissible free set of every point, inside V
  choose F u hF using fun z => red.dominance (q z)
  obtain ⟨mz, hmz⟩ : ∃ mz : Nat → Nat, ∀ z, mz z = ofBits6 fun k => decide (emb k ∈ F z) :=
    ⟨_, fun _ => rfl⟩
  have hFimg : ∀ z, F z = (univ.filter fun k : Fin 6 => emb k ∈ F z).image emb := by
    intro z
    ext i
    rw [mem_image]
    constructor
    · intro hi
      have hiV' : i ∈ V' := hVV' ((hF z).1 hi)
      obtain ⟨k, hk⟩ := hsurj i hiV'
      exact ⟨k, by rw [mem_filter]; exact ⟨mem_univ _, hk ▸ hi⟩, hk⟩
    · rintro ⟨k, hk, rfl⟩
      rw [mem_filter] at hk
      exact hk.2
  have hpop : ∀ z, Bound.pop (mz z) = (F z).card := by
    intro z
    unfold Bound.pop
    rw [hFimg z, card_image_of_injective _ hemb_inj]
    congr 1
    apply filter_congr
    intro k _
    rw [hmz, testBit_ofBits6, decide_eq_true_eq]
  have hmember : ∀ z s, Bound.member (mz z) s = true →
      s ≠ 0 ∧ ∀ k : Fin 6, s.testBit k = true → emb k ∈ F z := by
    intro z s h
    unfold Bound.member Bound.sub at h
    rw [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at h
    refine ⟨h.1, fun k hk => ?_⟩
    have := h.2 k hk
    rw [hmz, testBit_ofBits6, decide_eq_true_eq] at this
    exact this
  have hmemcls : ∀ z s, z < 64 → s < 64 → Bound.member (mz z) s = true →
      red.Y (q (z ^^^ s)) = red.Y (q z) → q (z ^^^ s) ∈ cls red.Y (q z) (F z) := by
    intro z s hz hs hm hY
    obtain ⟨hs0, hsub⟩ := hmember z s hm
    rw [mem_cls]
    refine ⟨?_, ?_, hY⟩
    · intro h
      have := hq_inj _ _ (xor_lt_64 hz hs) hz h
      exact xor_ne_self_of_ne_zero hs0 this
    · intro i hi
      by_cases hiV : i ∈ V'
      · obtain ⟨k, rfl⟩ := hsurj i hiV
        rw [hq_emb, hq_emb, Nat.testBit_xor]
        have hsk : s.testBit k = false := by
          cases h : s.testBit k
          · rfl
          · exact absurd (hsub k h) hi
        rw [hsk, Bool.xor_false]
      · rw [hq_out _ _ hiV, hq_out _ _ hiV]
  refine ⟨(Bound.Data.mk red.Y red.out q mz).assign, Bound.sat _ ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · -- distinct points have distinct build positions
    intro a b ha hb hab h
    dsimp only at h
    exact hab (hq_inj a b ha hb (red.out_injective h))
  · -- masks are points
    intro z _
    dsimp only
    rw [hmz]
    exact ofBits6_lt _
  · -- the chosen mask has at least three bits
    intro z _
    dsimp only
    unfold Bound.valid
    rw [decide_eq_true_eq, hpop]
    have := (hF z).2.1
    omega
  · -- a class member precedes its point
    intro z s hz hs hm hY
    dsimp only at hm hY ⊢
    exact (hF z).2.2.2 _ (hmemcls z s hz hs hm hY)
  · -- at most u class members
    intro z hz
    dsimp only
    have hb : Bound.bound (mz z) = u z := by
      unfold Bound.bound
      rw [hpop z]
      have := (hF z).2.1
      omega
    rw [hb]
    refine le_trans ?_ (hF z).2.2.1
    apply card_le_card_of_injOn (fun s => q (z ^^^ s))
    · intro s hs
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hs
      rw [Finset.mem_coe]
      exact hmemcls z s hz hs.1 hs.2.1 hs.2.2
    · intro s hs s' hs' h
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hs hs'
      have := hq_inj _ _ (xor_lt_64 hz hs.1) (xor_lt_64 hz hs'.1) h
      exact xor_left_injective_nat z this

end DecoderOptimality
