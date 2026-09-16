/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The norm is always the genuine Euclidean operator norm. The entry bound uses
the squared finite Cauchy--Schwarz inequality and avoids square-root algebra.
-/
import NLA.MF22.Definitions
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open scoped BigOperators

lemma spectralNorm_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : 0 ≤ spectralNorm A := norm_nonneg _

lemma spectralNorm_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    spectralNorm (A + B) ≤ spectralNorm A + spectralNorm B := by
  simpa only [spectralNorm, map_add] using
    norm_add_le (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) B)

lemma spectralNorm_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    spectralNorm (A - B) ≤ spectralNorm A + spectralNorm B := by
  simpa only [spectralNorm, map_sub] using
    norm_sub_le (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) B)

lemma spectralNorm_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    spectralNorm (A * B) ≤ spectralNorm A * spectralNorm B := by
  simpa only [spectralNorm, map_mul] using
    norm_mul_le (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) B)

lemma spectralNorm_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (A : Matrix ι ι ℂ) :
    spectralNorm (c • A) = ‖c‖ * spectralNorm A := by
  simp only [spectralNorm, map_smul, norm_smul]

lemma norm_entry_le_spectralNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (i j : ι) : ‖A i j‖ ≤ spectralNorm A := by
  let e : EuclideanSpace ℂ ι := PiLp.single 2 j (1 : ℂ)
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
  have he : ‖e‖ = 1 := by simp [e, PiLp.norm_single]
  have hv : (T e) i = A i j := by
    change (Matrix.mulVec A (Pi.single j (1 : ℂ))) i = A i j
    simp [Matrix.mulVec_single_one]
  calc
    ‖A i j‖ = ‖(T e) i‖ := congrArg norm hv.symm
    _ ≤ ‖T e‖ := PiLp.norm_apply_le (T e) i
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
    _ = spectralNorm A := by rw [he, mul_one]; rfl

lemma spectralNorm_le_of_square_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x : EuclideanSpace ℂ ι,
      ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2) :
    spectralNorm A ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg x))).mp
  simpa only [mul_pow] using h x

theorem complex_entry_norm_bound (ι : Type) [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hA : ∀ r s : ι, ‖A r s‖ ≤ B) :
    spectralNorm A ≤ (Fintype.card ι : ℝ) * B := by
  apply spectralNorm_le_of_square_bound A _ (mul_nonneg (Nat.cast_nonneg _) hB)
  intro x
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A
  have hrow (i : ι) :
      ‖(T x) i‖ ≤ ∑ j : ι, B * ‖x j‖ := by
    change ‖∑ j : ι, A i j * x j‖ ≤ _
    calc
      _ ≤ ∑ j : ι, ‖A i j * x j‖ := norm_sum_le _ _
      _ ≤ ∑ j : ι, B * ‖x j‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)
  have hcs : (∑ j : ι, B * ‖x j‖) ^ 2 ≤
      ((Fintype.card ι : ℝ) * B ^ 2) * ‖x‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
      (fun _ : ι => B) (fun j => ‖x j‖)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← EuclideanSpace.norm_sq_eq] using h
  have hrowSq (i : ι) : ‖(T x) i‖ ^ 2 ≤
      ((Fintype.card ι : ℝ) * B ^ 2) * ‖x‖ ^ 2 := by
    apply le_trans _ hcs
    exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg
      (fun j _ => mul_nonneg hB (norm_nonneg (x j))))).mpr (hrow i)
  calc
    ‖T x‖ ^ 2 = ∑ i : ι, ‖(T x) i‖ ^ 2 := EuclideanSpace.norm_sq_eq _
    _ ≤ ∑ _i : ι, ((Fintype.card ι : ℝ) * B ^ 2) * ‖x‖ ^ 2 :=
      Finset.sum_le_sum (fun i _ => hrowSq i)
    _ = ((Fintype.card ι : ℝ) * B) ^ 2 * ‖x‖ ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

#assert_trust kernel complex_entry_norm_bound
#print axioms complex_entry_norm_bound

end NLA.MF22
