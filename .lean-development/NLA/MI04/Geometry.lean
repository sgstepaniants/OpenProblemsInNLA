/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Normalize arbitrary orthogonal vectors symbolically, then use a three-coordinate
complex pair to detect the oriented area of any three diagonal values.
-/
import NLA.MI04.BasisTransport

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04

lemma matrixCoefficient_smul {n : ℕ} (X : Square n) (u v : CVector (Fin n)) (c d : ℂ) :
    matrixCoefficient X (c • u) (d • v) = star c * d * matrixCoefficient X u v := by
  simp [matrixCoefficient, map_smul, inner_smul_left, inner_smul_right,
    Complex.star_def, mul_assoc, mul_left_comm]

lemma complex_normalize_unit {n : ℕ} (u : CVector (Fin n)) (hu : u ≠ 0) :
    ‖((‖u‖⁻¹ : ℝ) : ℂ) • u‖ = 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg u), inv_mul_cancel₀ (norm_pos_iff.mpr hu).ne']

lemma pair_symmetry_all_vectors {n : ℕ} (X : Square n) (hX : PairMagnitudeSymmetry X)
    (u v : CVector (Fin n)) (huv : inner ℂ u v = 0) :
    ‖matrixCoefficient X u v‖ = ‖matrixCoefficient X v u‖ := by
  by_cases hu : u = 0
  · simp [hu, matrixCoefficient]
  by_cases hv : v = 0
  · simp [hv, matrixCoefficient]
  let c : ℂ := ((‖u‖⁻¹ : ℝ) : ℂ)
  let d : ℂ := ((‖v‖⁻¹ : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast inv_ne_zero (norm_pos_iff.mpr hu).ne'
  have hd : d ≠ 0 := by
    dsimp [d]
    exact_mod_cast inv_ne_zero (norm_pos_iff.mpr hv).ne'
  have hcu : ‖c • u‖ = 1 := complex_normalize_unit u hu
  have hdv : ‖d • v‖ = 1 := complex_normalize_unit v hv
  have horth : inner ℂ (c • u) (d • v) = 0 := by
    simp [inner_smul_left, inner_smul_right, huv]
  have h := hX (c • u) (d • v) hcu hdv horth
  simp only [matrixCoefficient_smul, norm_mul, norm_star] at h
  rw [mul_comm ‖d‖ ‖c‖] at h
  exact mul_left_cancel₀
    (mul_ne_zero (norm_pos_iff.mpr hc).ne' (norm_pos_iff.mpr hd).ne') h

lemma diagonal_coordinateUnit {n : ℕ} (z : Fin n → ℂ) (j : Fin n) :
    Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (Matrix.diagonal z) (coordinateUnit j) =
      z j • coordinateUnit j := by
  ext i
  by_cases hij : i = j
  · subst i
    simp [euclidean_matrix_apply, Matrix.diagonal, coordinateUnit_apply, PiLp.smul_apply]
  · simp [euclidean_matrix_apply, Matrix.diagonal, coordinateUnit_apply,
      PiLp.smul_apply, hij]

lemma equal_opposite_I_norm_im_zero (a b : ℂ) (h : ‖a + Complex.I * b‖ = ‖a - Complex.I * b‖) :
    (a * star b).im = 0 := by
  have hs : Complex.normSq (a + Complex.I * b) = Complex.normSq (a - Complex.I * b) := by
    simpa only [Complex.normSq_eq_norm_sq] using congrArg (fun x : ℝ => x ^ 2) h
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def] at hs ⊢
  nlinarith

theorem diagonal_pair_collinearity {n : ℕ} (hn : 1 ≤ n) (z : Fin n → ℂ)
    (hz : PairMagnitudeSymmetry (Matrix.diagonal z)) :
    ∀ i j k : Fin n, ((z i - z k) * star (z j - z k)).im = 0 := by
  intro i j k
  by_cases hij : i = j
  · subst j
    simp [Complex.star_def, Complex.mul_im] <;> ring
  by_cases hik : i = k
  · subst k
    simp
  by_cases hjk : j = k
  · subst k
    simp
  let u : CVector (Fin n) := coordinateUnit i + coordinateUnit j + coordinateUnit k
  let v : CVector (Fin n) := coordinateUnit i + Complex.I • coordinateUnit j -
    (1 + Complex.I) • coordinateUnit k
  have horth : inner ℂ u v = 0 := by
    simp [u, v, inner_add_left, inner_add_right, inner_sub_right, inner_smul_right,
      inner_coordinateUnit_left, coordinateUnit_apply,
      hij, Ne.symm hij, hik, Ne.symm hik, hjk, Ne.symm hjk] <;> ring
  have hleft : matrixCoefficient (Matrix.diagonal z) u v =
      (z i - z k) + Complex.I * (z j - z k) := by
    simp [matrixCoefficient, u, v, map_add, map_sub, map_smul, diagonal_coordinateUnit,
      inner_add_left, inner_add_right, inner_sub_right, inner_smul_right,
      inner_coordinateUnit_left, coordinateUnit_apply,
      hij, Ne.symm hij, hik, Ne.symm hik, hjk, Ne.symm hjk] <;> ring
  have hright : matrixCoefficient (Matrix.diagonal z) v u =
      (z i - z k) - Complex.I * (z j - z k) := by
    simp [matrixCoefficient, u, v, map_add, map_smul, diagonal_coordinateUnit,
      inner_add_left, inner_add_right, inner_sub_left, inner_smul_left, inner_smul_right,
      inner_coordinateUnit_left, coordinateUnit_apply, Complex.star_def,
      hij, Ne.symm hij, hik, Ne.symm hik, hjk, Ne.symm hjk] <;> ring
  have h := pair_symmetry_all_vectors (Matrix.diagonal z) hz u v horth
  rw [hleft, hright] at h
  exact equal_opposite_I_norm_im_zero (z i - z k) (z j - z k) h

#print axioms diagonal_pair_collinearity
#assert_trust kernel diagonal_pair_collinearity

end NLA.MI04
