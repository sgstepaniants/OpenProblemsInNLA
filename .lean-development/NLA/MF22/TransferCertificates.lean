/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

A fixed leading-block multiplication removes all inverse entries before the
four-dimensional determinant is expanded. The cofactor needs only one
three-dimensional sparse minor. There is no computation in the growing n.
-/
import NLA.MF22.LeadingBlock
import Mathlib.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open Polynomial
open scoped BigOperators

noncomputable section

lemma companion_pencil_det (a b c d e f g h z w : ℂ) :
    Matrix.det !![a, b, c, d; e, f, g, h; -z, 0, w, 0; 0, -z, 0, w] =
      (a * w + c * z) * (f * w + h * z) -
        (b * w + d * z) * (e * w + g * z) := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_four]
  norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove,
    Fin.lt_def, Fin.ext_iff,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

def leadingLift (ρ : ℝ) : Square 4 :=
  !![coefficientA ρ, coefficientB ρ, 0, 0;
    coefficientB ρ, coefficientD ρ, 0, 0;
    0, 0, 1, 0; 0, 0, 0, 1]

def transferLift (ρ : ℝ) : Square 4 :=
  !![24 * (ρ : ℂ), -96 * Complex.I, -coefficientF ρ, -coefficientC ρ;
    -96 * Complex.I, -24 * (ρ : ℂ), -coefficientC ρ, -coefficientE ρ;
    1, 0, 0, 0; 0, 1, 0, 0]

lemma transferMatrix_row_zero (ρ : ℝ) (j : Fin 4) :
    transferMatrix ρ 0 j = ((leadingBlock ρ)⁻¹ * transferRhs ρ) 0 j := by
  fin_cases j <;> rfl

lemma transferMatrix_row_one (ρ : ℝ) (j : Fin 4) :
    transferMatrix ρ 1 j = ((leadingBlock ρ)⁻¹ * transferRhs ρ) 1 j := by
  fin_cases j <;> rfl

lemma leadingLift_det (ρ : ℝ) : (leadingLift ρ).det = 24 * leadingScalar ρ := by
  calc
    _ = coefficientA ρ * coefficientD ρ - coefficientB ρ * coefficientB ρ := by
      simpa [leadingLift] using companion_pencil_det
        (coefficientA ρ) (coefficientB ρ) 0 0
        (coefficientB ρ) (coefficientD ρ) 0 0 0 1
    _ = (leadingBlock ρ).det := by rw [leadingBlock, Matrix.det_fin_two_of]
    _ = _ := leadingBlock_det ρ

lemma leadingLift_transfer (ρ : ℝ) (hρ : 0 < ρ) :
    leadingLift ρ * transferMatrix ρ = transferLift ρ := by
  have htop : leadingBlock ρ * ((leadingBlock ρ)⁻¹ * transferRhs ρ) = transferRhs ρ := by
    rw [← Matrix.mul_assoc, (leading_block_invertible ρ hρ).2.2.1, Matrix.one_mul]
  ext i j
  fin_cases i
  · have h := congrArg (fun M : Matrix (Fin 2) (Fin 4) ℂ => M 0 j) htop
    simpa [leadingLift, transferLift, transferRhs, leadingBlock, Matrix.mul_apply,
      Fin.sum_univ_four, Fin.sum_univ_two, transferMatrix_row_zero,
      transferMatrix_row_one] using h
  · have h := congrArg (fun M : Matrix (Fin 2) (Fin 4) ℂ => M 1 j) htop
    simpa [leadingLift, transferLift, transferRhs, leadingBlock, Matrix.mul_apply,
      Fin.sum_univ_four, Fin.sum_univ_two, transferMatrix_row_zero,
      transferMatrix_row_one] using h
  · fin_cases j <;> simp [leadingLift, transferLift, transferMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
  · fin_cases j <;> simp [leadingLift, transferLift, transferMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

lemma lifted_pencil (ρ : ℝ) (hρ : 0 < ρ) (t z : ℂ) :
    leadingLift ρ * (t • (1 : Square 4) - z • transferMatrix ρ) =
      !![t * coefficientA ρ - z * (24 * (ρ : ℂ)),
          t * coefficientB ρ + z * (96 * Complex.I), z * coefficientF ρ, z * coefficientC ρ;
        t * coefficientB ρ + z * (96 * Complex.I),
          t * coefficientD ρ + z * (24 * (ρ : ℂ)), z * coefficientC ρ, z * coefficientE ρ;
        -z, 0, t, 0; 0, -z, 0, t] := by
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.mul_smul, leadingLift_transfer ρ hρ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [leadingLift, transferLift, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

lemma homogeneous_pencil_certificate (ρ : ℝ) (hρ : 0 < ρ) (t z : ℂ) :
    (24 * leadingScalar ρ) * (t • (1 : Square 4) - z • transferMatrix ρ).det =
      24 * (leadingScalar ρ * t ^ 4 + middleScalar ρ * t ^ 3 * z +
        centralScalar ρ * t ^ 2 * z ^ 2 + star (middleScalar ρ) * t * z ^ 3 +
        star (leadingScalar ρ) * z ^ 4) := by
  rw [← leadingLift_det, ← Matrix.det_mul, lifted_pencil ρ hρ, companion_pencil_det]
  simp only [conjugate_leadingScalar, conjugate_middleScalar]
  unfold coefficientA coefficientB coefficientC coefficientD coefficientE coefficientF
    leadingScalar middleScalar centralScalar
  ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four] <;> ring

lemma scalar_eq_smul_one (t : ℂ) : Matrix.scalar (Fin 4) t = t • (1 : Square 4) := by
  ext i j
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp_all

lemma transfer_charpoly (ρ : ℝ) (hρ : 0 < ρ) :
    (transferMatrix ρ).charpoly = C ((leadingScalar ρ)⁻¹) * quartic ρ := by
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, scalar_eq_smul_one, eval_mul, eval_C]
  have h := homogeneous_pencil_certificate ρ hρ t 1
  have he : leadingScalar ρ * (t • (1 : Square 4) - transferMatrix ρ).det =
      (quartic ρ).eval t := by
    simp only [one_smul, one_pow, mul_one] at h
    simp only [quartic, eval_add, eval_mul, eval_pow, eval_C, eval_X]
    linear_combination (1 / 24 : ℂ) * h
  apply (mul_left_cancel₀ (leading_scalar_ne_zero ρ hρ))
  rw [← mul_assoc, mul_inv_cancel₀ (leading_scalar_ne_zero ρ hρ), one_mul]
  exact he

lemma transfer_denominator (ρ : ℝ) (hρ : 0 < ρ) (z : ℂ) :
    (1 - z • transferMatrix ρ).det = (denominator ρ).eval z / leadingScalar ρ := by
  apply (eq_div_iff (leading_scalar_ne_zero ρ hρ)).mpr
  have h := homogeneous_pencil_certificate ρ hρ 1 z
  simp only [one_smul, one_pow, mul_one] at h
  simp only [denominator, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  linear_combination (1 / 24 : ℂ) * h

lemma transfer_cofactor_form (ρ : ℝ) (z : ℂ) :
    (1 - z • transferMatrix ρ).adjugate 0 0 =
      1 - z * transferMatrix ρ 1 1 - z ^ 2 * transferMatrix ρ 1 3 := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  norm_num [Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove,
    Fin.lt_def, Fin.ext_iff,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, transferMatrix,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

lemma transfer_numerator (ρ : ℝ) (hρ : 0 < ρ) (z : ℂ) :
    (1 - z • transferMatrix ρ).adjugate 0 0 =
      (numerator ρ).eval z / leadingScalar ρ := by
  rw [transfer_cofactor_form, transferMatrix_row_one, transferMatrix_row_one,
    leadingBlock_inv]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  change 1 - z * (((24 * leadingScalar ρ)⁻¹ * (-coefficientB ρ)) * (-96 * Complex.I) +
      ((24 * leadingScalar ρ)⁻¹ * coefficientA ρ) * (-24 * (ρ : ℂ))) -
      z ^ 2 * (((24 * leadingScalar ρ)⁻¹ * (-coefficientB ρ)) * (-coefficientC ρ) +
      ((24 * leadingScalar ρ)⁻¹ * coefficientA ρ) * (-coefficientE ρ)) = _
  simp only [numerator, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  field_simp [leading_scalar_ne_zero ρ hρ] <;>
    unfold coefficientA coefficientB coefficientC coefficientE leadingScalar <;>
    ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four] <;> ring

theorem transfer_polynomial_certificates (ρ : ℝ) (hρ : 0 < ρ) :
    (transferMatrix ρ).charpoly = C ((leadingScalar ρ)⁻¹) * quartic ρ ∧
    ∀ z : ℂ,
      (1 - z • transferMatrix ρ).det = (denominator ρ).eval z / leadingScalar ρ ∧
      (1 - z • transferMatrix ρ).adjugate 0 0 =
        (numerator ρ).eval z / leadingScalar ρ := by
  exact ⟨transfer_charpoly ρ hρ, fun z =>
    ⟨transfer_denominator ρ hρ z, transfer_numerator ρ hρ z⟩⟩

#assert_trust kernel transfer_polynomial_certificates
#print axioms transfer_polynomial_certificates

end
end NLA.MF22
