/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The actual adjugate at a singular reciprocal-root pencil lies in the simple
spectral subspace on both sides. Cyclic trace and the genuine rank-one
sandwich convert scalar cancellation into a contradiction with N/d coprimality.
-/
import NLA.MF22.Coprime
import NLA.MF22.EigenEvaluation
import NLA.MF22.ProjectorRank
import NLA.MF22.SpectralAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open Polynomial
open scoped BigOperators

lemma trace_boundary_mul (A : Square 4) : Matrix.trace (boundaryOuter * A) = A 0 0 := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, boundaryOuter, boundaryVector,
    Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail]

lemma trace_zero_of_boundary_sandwich (P A : Square 4) (hleft : P * A = A)
    (hright : A * P = A) (hsandwich : P * boundaryOuter * P = 0) : A 0 0 = 0 := by
  calc
    A 0 0 = Matrix.trace (boundaryOuter * A) := (trace_boundary_mul A).symm
    _ = Matrix.trace (boundaryOuter * (P * A * P)) := by rw [hleft, hright]
    _ = Matrix.trace ((boundaryOuter * P * A) * P) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (P * (boundaryOuter * P * A)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((P * boundaryOuter * P) * A) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hsandwich, Matrix.zero_mul, Matrix.trace_zero]

lemma reciprocal_root_pencil_det (ρ : ℝ) (hρ : 0 < ρ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots) (i : Fin 4) :
    (1 - (roots i)⁻¹ • transferMatrix ρ).det = 0 := by
  have hi : roots i ≠ 0 := (hroots.2.1 i).1
  have hroot : (quartic ρ).eval (roots i) = 0 := (hroots.2.1 i).2
  have hc : (Matrix.scalar (Fin 4) (roots i) - transferMatrix ρ).det = 0 := by
    rw [← Matrix.eval_charpoly, (transfer_polynomial_certificates ρ hρ).1,
      eval_mul, eval_C, hroot, mul_zero]
  have he : 1 - (roots i)⁻¹ • transferMatrix ρ =
      (roots i)⁻¹ • (Matrix.scalar (Fin 4) (roots i) - transferMatrix ρ) := by
    rw [scalar_eq_smul_one, smul_sub, smul_smul, inv_mul_cancel₀ hi, one_smul]
  rw [he, Matrix.det_smul, hc, mul_zero]

lemma singular_pencil_adjugate_eigen (T : Square 4) (z : ℂ) (hz : z ≠ 0)
    (hd : (1 - z⁻¹ • T).det = 0) :
    T * (1 - z⁻¹ • T).adjugate = z • (1 - z⁻¹ • T).adjugate ∧
    (1 - z⁻¹ • T).adjugate * T = z • (1 - z⁻¹ • T).adjugate := by
  constructor
  · have h := Matrix.mul_adjugate (1 - z⁻¹ • T)
    rw [hd, zero_smul, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul] at h
    have he := congrArg (fun A : Square 4 => z • A) (sub_eq_zero.mp h)
    simpa only [smul_smul, mul_inv_cancel₀ hz, one_smul] using he.symm
  · have h := Matrix.adjugate_mul (1 - z⁻¹ • T)
    rw [hd, zero_smul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul] at h
    have he := congrArg (fun A : Square 4 => z • A) (sub_eq_zero.mp h)
    simpa only [smul_smul, mul_inv_cancel₀ hz, one_smul] using he.symm

lemma spectralProjector_boundary_entry_ne_zero (ρ : ℝ) (hρ : 0 < ρ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots) (i : Fin 4) :
    spectralProjector ρ roots i 0 0 ≠ 0 := by
  let B : Square 4 := 1 - (roots i)⁻¹ • transferMatrix ρ
  let A : Square 4 := B.adjugate
  let P : Square 4 := spectralProjector ρ roots i
  have hd : B.det = 0 := reciprocal_root_pencil_det ρ hρ roots hroots i
  have heigen := singular_pencil_adjugate_eigen (transferMatrix ρ) (roots i)
    (hroots.2.1 i).1 hd
  have heval : (Lagrange.basis Finset.univ roots i).eval (roots i) = 1 := by
    simpa using lagrange_basis_eval_node roots hroots.1 i i
  have hleft : P * A = A := by
    simpa only [P, spectralProjector, heval, one_smul] using
      aeval_mul_of_eigenmatrix (transferMatrix ρ) A (roots i) heigen.1
        (Lagrange.basis Finset.univ roots i)
  have hright : A * P = A := by
    simpa only [P, spectralProjector, heval, one_smul] using
      mul_aeval_of_eigenmatrix (transferMatrix ρ) A (roots i) heigen.2
        (Lagrange.basis Finset.univ roots i)
  have hden : (denominator ρ).eval ((roots i)⁻¹) = 0 := by
    have h := ((transfer_polynomial_certificates ρ hρ).2 ((roots i)⁻¹)).1
    change B.det = _ at h
    rw [hd] at h
    exact (div_eq_zero_iff.mp h.symm).resolve_right (leading_scalar_ne_zero ρ hρ)
  have hnum : (numerator ρ).eval ((roots i)⁻¹) ≠ 0 := by
    intro hn
    exact numerator_denominator_coprime ρ hρ ((roots i)⁻¹) hn hden
  have hentry : A 0 0 ≠ 0 := by
    change (1 - (roots i)⁻¹ • transferMatrix ρ).adjugate 0 0 ≠ 0
    rw [((transfer_polynomial_certificates ρ hρ).2 ((roots i)⁻¹)).2]
    exact div_ne_zero hnum (leading_scalar_ne_zero ρ hρ)
  intro hzero
  have hsandwich : P * boundaryOuter * P = 0 := by
    have h := spectralProjector_boundary_sandwich_of_charpoly ρ roots hroots
      (transfer_polynomial_certificates ρ hρ).1 i
    simpa only [hzero, zero_smul] using h
  exact hentry (trace_zero_of_boundary_sandwich P A hleft hright hsandwich)

theorem dominant_projector (ρ : ℝ) (hρ : 0 < ρ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots) :
    dominantGamma ρ roots ≠ 0 ∧
    spectralProjector ρ roots 3 * boundaryOuter * spectralProjector ρ roots 3 =
      dominantGamma ρ roots • spectralProjector ρ roots 3 := by
  exact ⟨spectralProjector_boundary_entry_ne_zero ρ hρ roots hroots 3,
    spectralProjector_boundary_sandwich_of_charpoly ρ roots hroots
      (transfer_polynomial_certificates ρ hρ).1 3⟩

#assert_trust kernel dominant_projector
#print axioms dominant_projector

end NLA.MF22
