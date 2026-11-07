import DecoderOptimality.Main
import Mathlib.Tactic.NormNum

namespace DecoderOptimality.Family

open Finset

def trunc {n : Nat} (x : Fin (n + 1) → Bool) : Fin n → Bool :=
  fun i => x i.castSucc

def extendedSet {n : Nat} (F : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  F.image fun i => i.castSucc

theorem castSucc_injective (n : Nat) : Function.Injective (fun i : Fin n => i.castSucc) := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun z : Fin (n + 1) => z.val) h

theorem extendedSet_card {n : Nat} (F : Finset (Fin n)) : (extendedSet F).card = F.card := by
  exact card_image_of_injective _ (castSucc_injective n)

theorem mem_extendedSet {n : Nat} (F : Finset (Fin n)) (i : Fin n) :
    i.castSucc ∈ extendedSet F ↔ i ∈ F := by
  constructor
  · intro h
    obtain ⟨j, hj, heq⟩ := mem_image.mp h
    have hji := castSucc_injective n heq
    simpa [hji] using hj
  · intro h
    exact mem_image.mpr ⟨i, h, rfl⟩

theorem last_not_extendedSet {n : Nat} (F : Finset (Fin n)) :
    Fin.last n ∉ extendedSet F := by
  intro h
  obtain ⟨i, _, heq⟩ := mem_image.mp h
  have hv := congrArg Fin.val heq
  have hi := i.isLt
  simp at hv
  omega

theorem pattern_ext {n : Nat} {x y : Fin (n + 1) → Bool}
    (h : trunc x = trunc y) (hlast : x (Fin.last n) = y (Fin.last n)) : x = y := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hlast
  · exact congrFun h j

def digit (b : Bool) : Nat := if b then 1 else 0

theorem digit_le (b : Bool) : digit b ≤ 1 := by
  cases b <;> decide

#check digit_le

/-- Add one input and one allowed LUT pin, duplicating the output order.
    The free-set budget n-K+1 is preserved. -/
def liftReduced {n K : Nat} (red : Reduced n K) : Reduced (n + 1) (K + 1) := by
  classical
  let Y : (Fin (n + 1) → Bool) → Bool := fun x => red.Y (trunc x)
  let out : (Fin (n + 1) → Bool) → Nat :=
    fun x => 2 * red.out (trunc x) + digit (x (Fin.last n))
  refine {
    Y := Y
    V := extendedSet red.V
    card_V := ?_
    ignores := ?_
    out := out
    out_injective := ?_
    admissible := ?_
  }
  · rw [extendedSet_card]
    exact red.card_V.trans (Nat.le_succ K)
  · intro x y h
    apply red.ignores
    intro i hi
    exact h i.castSucc ((mem_extendedSet red.V i).mpr hi)
  · intro x y h
    change 2 * red.out (trunc x) + digit (x (Fin.last n)) =
      2 * red.out (trunc y) + digit (y (Fin.last n)) at h
    have hx := digit_le (x (Fin.last n))
    have hy := digit_le (y (Fin.last n))
    have ho : red.out (trunc x) = red.out (trunc y) := by omega
    have hd : digit (x (Fin.last n)) = digit (y (Fin.last n)) := by omega
    have hb : x (Fin.last n) = y (Fin.last n) := by
      cases hxb : x (Fin.last n) <;> cases hyb : y (Fin.last n) <;> simp_all [digit]
    exact pattern_ext (red.out_injective ho) hb
  · intro q
    obtain ⟨F, u, hsize, hadm⟩ := red.admissible (trunc q)
    have hlast := last_not_extendedSet F
    have last_eq : ∀ x ∈ cls Y q (extendedSet F), x (Fin.last n) = q (Fin.last n) := by
      intro x hx
      exact (mem_cls.mp hx).2.1 _ hlast
    have mapped : ∀ x ∈ cls Y q (extendedSet F), trunc x ∈ cls red.Y (trunc q) F := by
      intro x hx
      have hc := mem_cls.mp hx
      apply mem_cls.mpr
      refine ⟨?_, ?_, hc.2.2⟩
      · intro h
        exact hc.1 (pattern_ext h (last_eq x hx))
      · intro i hi
        exact hc.2.1 i.castSucc (fun hm => hi ((mem_extendedSet F i).mp hm))
    have inj : Set.InjOn trunc (↑(cls Y q (extendedSet F)) : Set (Fin (n + 1) → Bool)) := by
      intro x hx y hy h
      exact pattern_ext h ((last_eq x hx).trans (last_eq y hy).symm)
    have subset : (cls Y q (extendedSet F)).image trunc ⊆ cls red.Y (trunc q) F := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      exact mapped y hy
    have hcard : (cls Y q (extendedSet F)).card ≤ (cls red.Y (trunc q) F).card := by
      calc
        _ = ((cls Y q (extendedSet F)).image trunc).card := (card_image_iff.mpr inj).symm
        _ ≤ _ := card_le_card subset
    refine ⟨extendedSet F, u, ?_, hcard.trans hadm.1, ?_⟩
    · rw [extendedSet_card]
      have heq : n + 1 - (K + 1) = n - K := by omega
      simpa [heq] using hsize
    · intro x hx
      have ho := hadm.2 (trunc x) (mapped x hx)
      have hx1 := digit_le (x (Fin.last n))
      have hq1 := digit_le (q (Fin.last n))
      change 2 * red.out (trunc x) + digit (x (Fin.last n)) <
        2 * red.out (trunc q) + digit (q (Fin.last n))
      omega

theorem noReduced86 (red : Reduced 8 6) : False := by
  obtain ⟨a, ha⟩ := bridge red
  have hu := Certificate.unsat a
  unfold Std.Sat.CNF.Sat at ha
  rw [ha] at hu
  cases hu

theorem lowerBoundK5 (net : Network 7 5) (hdec : net.computesDecoder) :
    130 ≤ net.nodes.size := by
  apply Nat.le_of_not_lt
  intro h
  have hsize : net.nodes.size ≤ 2 ^ 7 + 1 := by norm_num; omega
  obtain ⟨red⟩ := reduce net (by decide) (by decide) hdec hsize
  exact noReduced86 (liftReduced red)

theorem lowerBoundK4 (net : Network 6 4) (hdec : net.computesDecoder) :
    66 ≤ net.nodes.size := by
  apply Nat.le_of_not_lt
  intro h
  have hsize : net.nodes.size ≤ 2 ^ 6 + 1 := by norm_num; omega
  obtain ⟨red⟩ := reduce net (by decide) (by decide) hdec hsize
  exact noReduced86 (liftReduced (liftReduced red))

theorem lowerBoundK3 (net : Network 5 3) (hdec : net.computesDecoder) :
    34 ≤ net.nodes.size := by
  apply Nat.le_of_not_lt
  intro h
  have hsize : net.nodes.size ≤ 2 ^ 5 + 1 := by norm_num; omega
  obtain ⟨red⟩ := reduce net (by decide) (by decide) hdec hsize
  exact noReduced86 (liftReduced (liftReduced (liftReduced red)))

end DecoderOptimality.Family

#print axioms DecoderOptimality.Family.liftReduced
#print axioms DecoderOptimality.Family.lowerBoundK5
#print axioms DecoderOptimality.Family.lowerBoundK4
#print axioms DecoderOptimality.Family.lowerBoundK3
