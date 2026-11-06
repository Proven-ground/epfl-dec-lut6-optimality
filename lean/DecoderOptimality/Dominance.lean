import DecoderOptimality.Reduced

/-!
# Lemma 3 of the paper: free inputs inside `V`

An admissible pair `(F, u)` with `|F| ≥ base + u` is dominated by an admissible pair `(F', u')` with
`F' ⊆ V` and `|F'| = base + u'`. Removing a free input `w ∉ V` from `F`: since `Y` ignores `w`, the class
of `F` contains the class of `F \ {w}`, its image under flipping `w`, and `q` flipped at `w`, three
disjoint parts, so `|C_F| ≥ 2 |C_{F'}| + 1` and `(F \ {w}, u - 1)` is admissible. Once `F ⊆ V`, dropping
any input keeps admissibility. Induction on `|F|`.
-/

namespace DecoderOptimality

open Finset

variable {n : Nat}

theorem shrink (Y : (Fin n → Bool) → Bool) (V : Finset (Fin n))
    (hign : ∀ x x' : Fin n → Bool, (∀ i ∈ V, x i = x' i) → Y x = Y x')
    (out : (Fin n → Bool) → Nat) (q : Fin n → Bool) (base : Nat) :
    ∀ (c : Nat) (F : Finset (Fin n)) (u : Nat), F.card = c → base + u ≤ F.card →
      Admissible Y out q F u →
      ∃ (F' : Finset (Fin n)) (u' : Nat), F' ⊆ V ∧ F'.card = base + u' ∧ Admissible Y out q F' u' := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
  intro F u hc hle hadm
  by_cases hsub : F ⊆ V
  · by_cases heq : F.card = base + u
    · exact ⟨F, u, hsub, heq, hadm⟩
    · -- drop any input: the class shrinks
      have hpos : 0 < F.card := by omega
      obtain ⟨w, hw⟩ := card_pos.mp hpos
      have hcard : (F.erase w).card = c - 1 := by rw [card_erase_of_mem hw, hc]
      refine ih (c - 1) (by omega) (F.erase w) u hcard ?_ (hadm.mono (erase_subset w F))
      rw [card_erase_of_mem hw]
      omega
  · -- some free input lies outside V
    obtain ⟨w, hwF, hwV⟩ : ∃ w, w ∈ F ∧ w ∉ V := by
      by_contra h
      push_neg at h
      exact hsub fun w hw => h w hw
    have hflipY : ∀ x, Y (flip x w) = Y x := by
      intro x
      apply hign
      intro i hi
      exact flip_apply_of_ne x (fun h => hwV (h ▸ hi))
    -- q flipped at w is in the class, so u ≥ 1
    have hqF : flip q w ∈ cls Y q F := by
      rw [mem_cls]
      exact ⟨flip_ne q w, fun i hi => flip_apply_of_ne q (fun h => hi (h ▸ hwF)), hflipY q⟩
    have hu : 1 ≤ u := by
      have := card_pos.mpr ⟨_, hqF⟩
      have := hadm.1
      omega
    obtain ⟨F', hF'⟩ : ∃ F' : Finset (Fin n), F' = F.erase w := ⟨_, rfl⟩
    have hF'sub : F' ⊆ F := by rw [hF']; exact erase_subset w F
    have hwF' : w ∉ F' := by rw [hF']; simp
    have hS1sub : cls Y q F' ⊆ cls Y q F := cls_mono hF'sub
    have hS1w : ∀ x ∈ cls Y q F', x w = q w := by
      intro x hx
      rw [mem_cls] at hx
      exact hx.2.1 w hwF'
    -- the flipped copy of the smaller class, together with q flipped, also sits in the class of F
    have hS2sub : (insert q (cls Y q F')).image (fun x => flip x w) ⊆ cls Y q F := by
      intro y hy
      rw [mem_image] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [mem_insert] at hx
      have hxw : x w = q w := by
        rcases hx with hxq | hx
        · rw [hxq]
        · exact hS1w x hx
      have hxY : Y x = Y q := by
        rcases hx with hxq | hx
        · rw [hxq]
        · rw [mem_cls] at hx; exact hx.2.2
      have hxF : ∀ i, i ∉ F → x i = q i := by
        rcases hx with hxq | hx
        · intro i _; rw [hxq]
        · intro i hi
          rw [mem_cls] at hx
          exact hx.2.1 i (fun h => hi (hF'sub h))
      rw [mem_cls]
      refine ⟨?_, ?_, ?_⟩
      · intro h
        have := congrFun h w
        rw [flip_apply_self, hxw] at this
        cases q w <;> simp at this
      · intro i hi
        have hiw : i ≠ w := fun h => hi (h ▸ hwF)
        rw [flip_apply_of_ne x hiw]
        exact hxF i hi
      · rw [hflipY, hxY]
    have hdisj : Disjoint (cls Y q F') ((insert q (cls Y q F')).image (fun x => flip x w)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [mem_image] at hx2
      obtain ⟨y, hy, hyx⟩ := hx2
      have h1 := hS1w x hx1
      have hyw : y w = q w := by
        rw [mem_insert] at hy
        rcases hy with hyq | hy
        · rw [hyq]
        · exact hS1w y hy
      have := congrFun hyx w
      rw [flip_apply_self, hyw] at this
      rw [← this] at h1
      exact Bool.not_ne_self _ h1
    have hqS1 : q ∉ cls Y q F' := by
      intro h
      rw [mem_cls] at h
      exact h.1 rfl
    have hS2card : ((insert q (cls Y q F')).image (fun x => flip x w)).card = (cls Y q F').card + 1 := by
      rw [card_image_of_injective _ (flip_left_injective w), card_insert_of_notMem hqS1]
    have hle' : (cls Y q F').card + ((insert q (cls Y q F')).image (fun x => flip x w)).card
        ≤ (cls Y q F).card := by
      rw [← card_union_of_disjoint hdisj]
      exact card_le_card (union_subset hS1sub hS2sub)
    have hadm' : Admissible Y out q F' (u - 1) := by
      refine ⟨?_, fun x hx => hadm.2 x (hS1sub hx)⟩
      have := hadm.1
      omega
    have hcard : F'.card = c - 1 := by rw [hF', card_erase_of_mem hwF, hc]
    refine ih (c - 1) (by omega) F' (u - 1) hcard ?_ hadm'
    rw [hF', card_erase_of_mem hwF]
    omega

/-- Lemma 3: every output has an admissible pair inside `V` with exactly `n - K + 1 + u` free inputs. -/
theorem Reduced.dominance {K : Nat} (red : Reduced n K) (q : Fin n → Bool) :
    ∃ (F : Finset (Fin n)) (u : Nat), F ⊆ red.V ∧ F.card = n - K + 1 + u ∧
      Admissible red.Y red.out q F u := by
  obtain ⟨F, u, hle, hadm⟩ := red.admissible q
  exact shrink red.Y red.V red.ignores red.out q (n - K + 1) F.card F u rfl hle hadm

end DecoderOptimality
