/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Exact finite Green-kernel recurrence and boundary identities. These hold
before any asymptotic estimate and use the actual displayed transfer matrix.
-/
import NLA.MF22.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open scoped BigOperators

lemma boundary_product {ι : Type*} (A : Square 4) (B : Matrix (Fin 4) ι ℂ)
    (r : Fin 4) (s : ι) : (A * boundaryOuter * B) r s = A r 0 * B 0 s := by
  simp [Matrix.mul_apply, boundaryOuter, boundaryVector, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

lemma boundary_four_product {ι : Type*} (A B : Square 4) (G : Matrix (Fin 4) ι ℂ)
    (r : Fin 4) (s : ι) :
    (A * boundaryOuter * B * G) r s = A r 0 * (B * G) 0 s := by
  rw [Matrix.mul_assoc (A * boundaryOuter) B G]
  exact boundary_product A (B * G) r s

lemma transfer_shift_two {ι : Type*} (ρ : ℝ) (B : Matrix (Fin 4) ι ℂ) (s : ι) :
    (transferMatrix ρ * B) 2 s = B 0 s := by
  simp [Matrix.mul_apply, transferMatrix, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

lemma transfer_shift_three {ι : Type*} (ρ : ℝ) (B : Matrix (Fin 4) ι ℂ) (s : ι) :
    (transferMatrix ρ * B) 3 s = B 1 s := by
  simp [Matrix.mul_apply, transferMatrix, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]

lemma forcing_row_two (ρ : ℝ) (s : Fin 2) : forcingMatrix ρ 2 s = 0 := by
  fin_cases s <;> rfl

lemma forcing_row_three (ρ : ℝ) (s : Fin 2) : forcingMatrix ρ 3 s = 0 := by
  fin_cases s <;> rfl

lemma forward_kernel_step (T : Square 4) (G : Matrix (Fin 4) (Fin 2) ℂ)
    (j ell : ℕ) :
    (if ell < j + 1 then T ^ (j + 1 - 1 - ell) * G else 0) =
      T * (if ell < j then T ^ (j - 1 - ell) * G else 0) +
        (if ell = j then G else 0) := by
  by_cases hlt : ell < j
  · have hle : ell < j + 1 := by omega
    have hne : ell ≠ j := by omega
    have hp : j + 1 - 1 - ell = (j - 1 - ell) + 1 := by omega
    simp only [hlt, hle, hne, if_true, if_false, add_zero, hp, pow_succ', Matrix.mul_assoc]
  · by_cases he : ell = j
    · subst ell
      simp
    · have hle : ¬ell < j + 1 := by omega
      simp [hlt, he, hle]

lemma greenKernel_step (ρ : ℝ) (n j ell : ℕ) :
    greenKernel ρ n (j + 1) ell =
      transferMatrix ρ * greenKernel ρ n j ell +
        (if ell = j then forcingMatrix ρ else 0) := by
  unfold greenKernel
  rw [forward_kernel_step, Matrix.mul_sub, Matrix.mul_smul, pow_succ']
  simp only [Matrix.mul_assoc]
  abel

lemma greenKernel_shift_two (ρ : ℝ) (n j ell : ℕ) (s : Fin 2) :
    greenKernel ρ n (j + 1) ell 2 s = greenKernel ρ n j ell 0 s := by
  rw [greenKernel_step]
  simp only [Matrix.add_apply, transfer_shift_two, Matrix.ite_apply,
    forcing_row_two, Matrix.zero_apply, ite_self, add_zero]

lemma greenKernel_shift_three (ρ : ℝ) (n j ell : ℕ) (s : Fin 2) :
    greenKernel ρ n (j + 1) ell 3 s = greenKernel ρ n j ell 1 s := by
  rw [greenKernel_step]
  simp only [Matrix.add_apply, transfer_shift_three, Matrix.ite_apply,
    forcing_row_three, Matrix.zero_apply, ite_self, add_zero]

lemma greenKernel_initial_zero (ρ : ℝ) (n ell : ℕ) (r : Fin 4) (hr : r ≠ 0)
    (s : Fin 2) : greenKernel ρ n 0 ell r s = 0 := by
  simp only [greenKernel, Nat.not_lt_zero, if_false, pow_zero, Matrix.sub_apply,
    Matrix.zero_apply, Matrix.smul_apply, smul_eq_mul]
  rw [boundary_four_product]
  simp [Matrix.one_apply, hr]

lemma greenKernel_terminal_zero (ρ : ℝ) (n ell : ℕ) (hell : ell < n)
    (ha : boundaryScalar ρ n ≠ 0) (s : Fin 2) : greenKernel ρ n n ell 0 s = 0 := by
  simp only [greenKernel, hell, if_true, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, boundary_four_product]
  change (transferMatrix ρ ^ (n - 1 - ell) * forcingMatrix ρ) 0 s -
    (boundaryScalar ρ n)⁻¹ *
      (boundaryScalar ρ n * (transferMatrix ρ ^ (n - 1 - ell) * forcingMatrix ρ) 0 s) = 0
  field_simp [ha] <;> ring

#assert_trust kernel greenKernel_step
#assert_trust kernel greenKernel_terminal_zero

end NLA.MF22
