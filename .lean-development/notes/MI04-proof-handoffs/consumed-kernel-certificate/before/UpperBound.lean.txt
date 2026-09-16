/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

The scalar weighted-square bound is summed over every off-peak coordinate.
-/
import NLA.MI04.Punctured
import NLA.MI04.ScalarGeometry
import NLA.MI04.Correction

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder

namespace NLA.MI04
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma perturbed_gap_pos (d : ι → ℝ) (V : CMatrix ι) (a : ι)
    (hd : ∀ j, j ≠ a → d j ≤ (1 : ℝ) / 2) (ε : ℝ)
    (hε : 0 < ε) (hsmall : ε * (1 + spectralNorm V) < (1 : ℝ) / 4)
    (j : ι) (hj : j ≠ a) :
    (1 : ℝ) / 4 < 1 - d j - ε * spectralNorm V := by
  have hdj := hd j hj
  nlinarith

lemma upperCoefficient_nonneg (d : ι → ℝ) (V : CMatrix ι) (a : ι)
    (hd : ∀ j, j ≠ a → d j ≤ (1 : ℝ) / 2) (ε : ℝ)
    (hε : 0 < ε) (hsmall : ε * (1 + spectralNorm V) < (1 : ℝ) / 4) :
    0 ≤ upperCoefficient d V a ε := by
  unfold upperCoefficient
  apply Finset.sum_nonneg
  intro j _
  by_cases hj : j = a
  · simp [hj]
  · rw [if_neg hj]
    exact div_nonneg (Complex.normSq_nonneg _)
      (by have h := perturbed_gap_pos d V a hd ε hε hsmall j hj; linarith)

lemma scaled_weighted_square (q ε : ℝ) (hq : 0 < q) (c z w : ℂ) :
    2 * ε * (c * z * star w).re - q * Complex.normSq w ≤
      ε ^ 2 * Complex.normSq c * (Complex.normSq z / q) := by
  have h := weighted_square_bound q hq ((ε : ℂ) * c * z) w
  have hleft : (((ε : ℂ) * c * z) * star w).re = ε * (c * z * star w).re := by
    calc
      (((ε : ℂ) * c * z) * star w).re = ((ε : ℂ) * (c * z * star w)).re := by
        congr 1
        ring
      _ = ε * (c * z * star w).re := by simp [Complex.mul_re]
  have hright : Complex.normSq ((ε : ℂ) * c * z) / q =
      ε ^ 2 * Complex.normSq c * (Complex.normSq z / q) := by
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
    ring
  rw [hleft, hright] at h
  nlinarith only [h]

lemma perturbation_unit_vector_upper (d : ι → ℝ) (V : CMatrix ι) (a : ι)
    (ha : d a = 1) (hd : ∀ j, j ≠ a → d j ≤ (1 : ℝ) / 2)
    (hV : V.IsHermitian) (haa : V a a = 0) (ε : ℝ)
    (hε : 0 < ε) (hsmall : ε * (1 + spectralNorm V) < (1 : ℝ) / 4)
    (v : CVector ι) (hv : ‖v‖ = 1) :
    realQuadratic (perturbedDiagonal d V ε) v - 1 ≤
      ε ^ 2 * upperCoefficient d V a ε := by
  have hbound := perturbation_all_vector_bound d V a ha hV haa ε hε.le v
  rw [hv, one_pow] at hbound
  have hsum :
      (∑ j, if j = a then 0 else
        2 * ε * (v a * V j a * star (v j)).re -
          (1 - d j - ε * spectralNorm V) * Complex.normSq (v j)) ≤
      ε ^ 2 * Complex.normSq (v a) * upperCoefficient d V a ε := by
    unfold upperCoefficient
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j = a
    · simp [hj]
    · rw [if_neg hj, if_neg hj]
      apply scaled_weighted_square
      have h := perturbed_gap_pos d V a hd ε hε hsmall j hj
      linarith
  have hc : Complex.normSq (v a) ≤ 1 := by
    simpa only [hv, one_pow] using coordinate_normSq_le a v
  have hnonneg := upperCoefficient_nonneg d V a hd ε hε hsmall
  calc
    realQuadratic (perturbedDiagonal d V ε) v - 1 ≤
        ε ^ 2 * Complex.normSq (v a) * upperCoefficient d V a ε := hbound.trans hsum
    _ ≤ ε ^ 2 * upperCoefficient d V a ε := by
      have h := mul_le_mul_of_nonneg_left hc (sq_nonneg ε)
      simpa only [mul_one] using mul_le_mul_of_nonneg_right h hnonneg

variable [Nonempty ι]

lemma simple_peak_upper_bound (d : ι → ℝ) (V : CMatrix ι) (a : ι)
    (ha : d a = 1) (hd : ∀ j, j ≠ a → d j ≤ (1 : ℝ) / 2)
    (hV : V.IsHermitian) (haa : V a a = 0) (ε : ℝ)
    (hε : 0 < ε) (hsmall : ε * (1 + spectralNorm V) < (1 : ℝ) / 4) :
    (topValue (perturbedDiagonal d V ε) - 1) / ε ^ 2 ≤ upperCoefficient d V a ε := by
  obtain ⟨v, hv, he, _⟩ := topValue_attained (perturbedDiagonal d V ε)
  apply (div_le_iff₀ (sq_pos_of_pos hε)).mpr
  rw [← he, mul_comm (upperCoefficient d V a ε)]
  exact perturbation_unit_vector_upper d V a ha hd hV haa ε hε hsmall v hv

theorem simple_peak_sandwich (d : ι → ℝ) (V : CMatrix ι) (a : ι)
    (ha : d a = 1) (hd : ∀ j, j ≠ a → d j ≤ (1 : ℝ) / 2)
    (hV : V.IsHermitian) (haa : V a a = 0) (ε : ℝ)
    (hε : 0 < ε) (hsmall : ε * (1 + spectralNorm V) < (1 : ℝ) / 4) :
    (secondCoefficient d V a + ε * realQuadratic V (correctionVector d V a)) /
        (1 + ε ^ 2 * ‖correctionVector d V a‖ ^ 2) ≤
      (topValue (perturbedDiagonal d V ε) - 1) / ε ^ 2 ∧
    (topValue (perturbedDiagonal d V ε) - 1) / ε ^ 2 ≤
      upperCoefficient d V a ε :=
  ⟨simple_peak_lower_bound d V a ha hd hV haa ε hε,
    simple_peak_upper_bound d V a ha hd hV haa ε hε hsmall⟩

#print axioms simple_peak_sandwich
#assert_trust kernel simple_peak_sandwich

end NLA.MI04
