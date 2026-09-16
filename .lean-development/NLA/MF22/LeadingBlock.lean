/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The transfer construction uses the actual Mathlib nonsingular inverse.
Its fixed two-dimensional determinant is computed before any inversion.
-/
import NLA.MF22.ScalarCertificates
import Mathlib.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22

lemma leadingBlock_det (ρ : ℝ) :
    (leadingBlock ρ).det = 24 * leadingScalar ρ := by
  rw [leadingBlock, Matrix.det_fin_two_of]
  unfold coefficientA coefficientB coefficientD leadingScalar
  ring_nf <;> norm_num [Complex.I_sq] <;> ring

lemma leadingBlock_det_ne_zero (ρ : ℝ) (hρ : 0 < ρ) :
    (leadingBlock ρ).det ≠ 0 := by
  rw [leadingBlock_det]
  exact mul_ne_zero (by norm_num) (leading_scalar_ne_zero ρ hρ)

lemma leadingBlock_inv (ρ : ℝ) :
    (leadingBlock ρ)⁻¹ = (24 * leadingScalar ρ)⁻¹ •
      !![coefficientD ρ, -coefficientB ρ; -coefficientB ρ, coefficientA ρ] := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, leadingBlock_det]
  congr 1
  exact Matrix.adjugate_fin_two_of _ _ _ _

theorem leading_block_invertible (ρ : ℝ) (hρ : 0 < ρ) :
    leadingScalar ρ ≠ 0 ∧ (leadingBlock ρ).det = 24 * leadingScalar ρ ∧
    leadingBlock ρ * (leadingBlock ρ)⁻¹ = 1 ∧
    (leadingBlock ρ)⁻¹ * leadingBlock ρ = 1 := by
  have hd : IsUnit (leadingBlock ρ).det := isUnit_iff_ne_zero.mpr
    (leadingBlock_det_ne_zero ρ hρ)
  exact ⟨leading_scalar_ne_zero ρ hρ, leadingBlock_det ρ,
    Matrix.mul_nonsing_inv _ hd, Matrix.nonsing_inv_mul _ hd⟩

#assert_trust kernel leading_block_invertible
#print axioms leading_block_invertible

end NLA.MF22
