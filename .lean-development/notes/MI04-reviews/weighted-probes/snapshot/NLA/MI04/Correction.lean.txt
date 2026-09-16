/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Exact first-order correction and the lower half of the reviewed sandwich.
-/
import NLA.MI04.Coordinates
import NLA.MI04.Rayleigh

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder

namespace NLA.MI04
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] lemma correctionVector_apply (d : ι → ℝ) (V : CMatrix ι) (a j : ι) :
    correctionVector d V a j = if j = a then 0 else V j a / ((1 - d j : ℝ) : ℂ) :=
  rfl

@[simp] lemma correctionVector_at (d : ι → ℝ) (V : CMatrix ι) (a : ι) :
    correctionVector d V a a = 0 := by simp

lemma real_gap_product (z : ℂ) (g : ℝ) :
    (star z * (z / (g : ℂ))).re = Complex.normSq z / g := by
  rw [Complex.star_def, ← mul_div_assoc, ← Complex.normSq_eq_conj_mul_self]
  simp

lemma diagonal_gap_pos (d : ι → ℝ) (a : ι)
    (hd : ∀ j, j ≠ a → d j ≤ (1 : ℝ) / 2) (j : ι) (hj : j ≠ a) :
    0 < 1 - d j := by
  have h := hd j hj
  linarith

lemma correction_cross (d : ι → ℝ) (V : CMatrix ι) (a : ι)
    (hV : V.IsHermitian) :
    (inner ℂ (coordinateUnit a)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) V (correctionVector d V a))).re =
        secondCoefficient d V a := by
  rw [inner_coordinateUnit_left, euclidean_matrix_apply, Complex.re_sum]
  unfold secondCoefficient
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = a
  · subst j
    simp
  · rw [correctionVector_apply, if_neg hj, if_neg hj, ← hV.apply a j]
    exact real_gap_product (V j a) (1 - d j)

lemma correction_diagonal (d : ι → ℝ) (V : CMatrix ι) (a : ι)
    (hd : ∀ j, j ≠ a → d j ≤ (1 : ℝ) / 2) :
    realQuadratic (realDiagonal d) (correctionVector d V a) =
      ‖correctionVector d V a‖ ^ 2 - secondCoefficient d V a := by
  rw [realQuadratic_diagonal, norm_sq_eq_sum_normSq]
  unfold secondCoefficient
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = a
  · subst j
    simp
  · have hg := (diagonal_gap_pos d a hd j hj).ne'
    simp only [correctionVector_apply, if_neg hj, Complex.normSq_div,
      Complex.normSq_ofReal]
    field_simp [hg] <;> ring

lemma secondCoefficient_nonneg (d : ι → ℝ) (V : CMatrix ι) (a : ι)
    (hd : ∀ j, j ≠ a → d j ≤ (1 : ℝ) / 2) :
    0 ≤ secondCoefficient d V a := by
  unfold secondCoefficient
  apply Finset.sum_nonneg
  intro j _
  by_cases hj : j = a
  · simp [hj]
  · rw [if_neg hj]
    exact div_nonneg (Complex.normSq_nonneg _) (diagonal_gap_pos d a hd j hj).le

lemma inner_coordinate_realDiagonal (d : ι → ℝ) (a : ι) (v : CVector ι) :
    inner ℂ (coordinateUnit a)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (realDiagonal d) v) =
        (d a : ℂ) * v a := by
  rw [inner_coordinateUnit_left]
  change (Matrix.diagonal (fun j => (d j : ℂ)) *ᵥ WithLp.ofLp v) a = _
  exact Matrix.mulVec_diagonal _ _ _

lemma correction_trial_quadratic (d : ι → ℝ) (V : CMatrix ι) (a : ι)
    (ha : d a = 1) (hd : ∀ j, j ≠ a → d j ≤ (1 : ℝ) / 2)
    (hV : V.IsHermitian) (haa : V a a = 0) (ε : ℝ) :
    realQuadratic (perturbedDiagonal d V ε)
      (coordinateUnit a + (ε : ℂ) • correctionVector d V a) =
        1 + ε ^ 2 * (‖correctionVector d V a‖ ^ 2 + secondCoefficient d V a) +
          ε ^ 3 * realQuadratic V (correctionVector d V a) := by
  unfold perturbedDiagonal
  rw [realQuadratic_add, realQuadratic_smul_matrix,
    realQuadratic_real_perturbed_vector _ (realDiagonal_isHermitian d),
    realQuadratic_real_perturbed_vector _ hV,
    realQuadratic_coordinateUnit, realQuadratic_coordinateUnit,
    correction_diagonal d V a hd, correction_cross d V a hV,
    inner_coordinate_realDiagonal]
  simp only [realDiagonal, Matrix.diagonal_apply_eq, ha, Complex.ofReal_one,
    Complex.one_re, haa, Complex.zero_re, correctionVector_at, mul_zero, zero_add]
  ring

variable [Nonempty ι]

lemma simple_peak_lower_bound (d : ι → ℝ) (V : CMatrix ι) (a : ι)
    (ha : d a = 1) (hd : ∀ j, j ≠ a → d j ≤ (1 : ℝ) / 2)
    (hV : V.IsHermitian) (haa : V a a = 0) (ε : ℝ) (hε : 0 < ε) :
    (secondCoefficient d V a + ε * realQuadratic V (correctionVector d V a)) /
        (1 + ε ^ 2 * ‖correctionVector d V a‖ ^ 2) ≤
      (topValue (perturbedDiagonal d V ε) - 1) / ε ^ 2 := by
  have hden : 0 < 1 + ε ^ 2 * ‖correctionVector d V a‖ ^ 2 := by positivity
  have hsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  apply (div_le_div_iff₀ hden hsq).mpr
  have h := realQuadratic_le_top_mul_norm_sq (perturbedDiagonal d V ε)
    (coordinateUnit a + (ε : ℂ) • correctionVector d V a)
  rw [correction_trial_quadratic d V a ha hd hV haa ε,
    coordinateUnit_add_norm_sq a _ (correctionVector_at d V a) ε] at h
  nlinarith only [h]

#print axioms simple_peak_lower_bound
#assert_trust kernel simple_peak_lower_bound

end NLA.MI04
