import DecoderOptimality.Structure
import DecoderOptimality.Bridge
import DecoderOptimality.Certificate

/-!
# The theorem

No single-output LUT-6 network computes all 256 minterms of 8 inputs with 257 or fewer LUTs, at any depth,
with constants, buffers and inverters free.
-/

namespace DecoderOptimality

theorem lowerBound (net : Network 8 6) (hdec : net.computesDecoder) : 258 ≤ net.nodes.size := by
  apply Nat.le_of_not_lt
  intro h
  have hsize : net.nodes.size ≤ 2 ^ 8 + 1 := by
    have h256 : (2 : Nat) ^ 8 = 256 := by decide
    omega
  obtain ⟨red⟩ := reduce net (by decide) (by decide) hdec hsize
  obtain ⟨a, ha⟩ := bridge red
  have hu := Certificate.unsat a
  unfold Std.Sat.CNF.Sat at ha
  rw [ha] at hu
  cases hu

/-- Lemmas 1 and 2 alone, for every `n > K ≥ 1`: a decoder network has at least `2 ^ n + 1` nodes. -/
theorem lowerBound_general {n K : Nat} (net : Network n K) (hK : 1 ≤ K) (hnK : K < n)
    (hdec : net.computesDecoder) : 2 ^ n + 1 ≤ net.nodes.size :=
  two_pow_lt_size net hK hnK hdec

/-- The 7-input decoder needs 129 LUT-6 nodes. -/
theorem lowerBound7 (net : Network 7 6) (hdec : net.computesDecoder) : 129 ≤ net.nodes.size := by
  have h := two_pow_lt_size net (by decide) (by decide) hdec
  have h128 : (2 : Nat) ^ 7 = 128 := by decide
  omega

end DecoderOptimality

#print axioms DecoderOptimality.lowerBound
#print axioms DecoderOptimality.lowerBound_general
#print axioms DecoderOptimality.lowerBound7
