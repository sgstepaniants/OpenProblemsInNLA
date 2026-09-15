/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Every feasible perturbation is covered. For a nonzero new residual, all
inequalities are multiplied by its exact squared length, eliminating unit
vector normalization and square-root intervals. The zero-residual case is
handled separately by E*x=r. Attainment then transfers strictness to the
actual optimization-defined backward error.
-/
import NLA.IE17.Certificates
import NLA.IE17.Attainment
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical Matrix.Norms.L2Operator
noncomputable section
namespace NLA.IE17

theorem lowerD_quadratic (d : Vec 4) :
    realDot d (lowerD.mulVec d) =
      (normSq (residual witnessA witnessB witnessX2) * normSq d -
        realDot d (residual witnessA witnessB witnessX2) ^ 2 +
        realDot d (witnessA.mulVec witnessX2) ^ 2) / normSq witnessX2 := by
  simp only [lowerD, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, realDot_smul, realDot_add, realDot_sub, realDot_self,
    realDot_outer]
  ring

theorem lowerConvex_quadratic (d : Vec 4) :
    realDot d (lowerConvexMatrix.mulVec d) =
      (5 / 6 : ℝ) * normSq (witnessA.transpose.mulVec d) +
        (1 / 6 : ℝ) * realDot d (lowerD.mulVec d) := by
  rw [lowerConvexMatrix, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    realDot_add, realDot_smul, realDot_smul, realDot_cogram]

theorem every_second_perturbation_large (E : Mat 4 3)
    (hE : FeasiblePerturbation witnessA witnessB witnessX2 E) :
    (99 / 100 : ℝ) < spectralNorm E ^ 2 := by
  let d : Vec 4 := witnessB - (witnessA + E).mulVec witnessX2
  let r := residual witnessA witnessB witnessX2
  let z := witnessA.mulVec witnessX2
  let s := normSq witnessX2
  have hs : 0 < s := normSq_pos witness_before_termination.2.1
  have hs0 : normSq witnessX2 ≠ 0 := ne_of_gt hs
  have hex : E.mulVec witnessX2 = r - d := by
    dsimp [r, d, residual]
    rw [Matrix.add_mulVec]
    abel
  by_cases hd : d = 0
  · have hbound := normSq_mulVec_le E witnessX2
    rw [hex, hd, sub_zero] at hbound
    change normSq (residual witnessA witnessB witnessX2) ≤
      spectralNorm E ^ 2 * normSq witnessX2 at hbound
    rw [witness_squared_lengths.2.2.1, witness_squared_lengths.2.2.2] at hbound
    nlinarith
  have hnormal : (witnessA + E).transpose.mulVec d = 0 := by
    have hneg : (witnessA + E).mulVec witnessX2 - witnessB = -d := by
      dsimp [d]
      abel
    change (witnessA + E).transpose.mulVec ((witnessA + E).mulVec witnessX2 - witnessB) = 0 at hE
    rw [hneg, Matrix.mulVec_neg, neg_eq_zero] at hE
    exact hE
  have haE : witnessA.transpose.mulVec d + E.transpose.mulVec d = 0 := by
    simpa only [Matrix.transpose_add, Matrix.add_mulVec] using hnormal
  have ha : witnessA.transpose.mulVec d = -(E.transpose.mulVec d) := by
    calc
      _ = (witnessA.transpose.mulVec d + E.transpose.mulVec d) - E.transpose.mulVec d := by abel
      _ = _ := by rw [haE]; simp
  have hC : normSq (witnessA.transpose.mulVec d) ≤ spectralNorm E ^ 2 * normSq d := by
    rw [ha, normSq_neg]
    exact normSq_transpose_mulVec_le E d
  have hdotNew : realDot d ((witnessA + E).mulVec witnessX2) = 0 := by
    rw [realDot_comm]
    change dotProduct ((witnessA + E).mulVec witnessX2) d = 0
    rw [dot_mulVec_left, hnormal]
    simp [dotProduct]
  have hb : witnessB = d + (witnessA + E).mulVec witnessX2 := by
    dsimp [d]
    abel
  have hdb : realDot d witnessB = normSq d := by
    rw [hb, realDot_add, realDot_self, hdotNew, add_zero]
  have hdrz : realDot d r + realDot d z = normSq d := by
    rw [← realDot_add]
    dsimp [r, z, residual]
    rw [sub_add_cancel]
    exact hdb
  have hscaled : s * realDot d (lowerD.mulVec d) =
      normSq r * normSq d - realDot d r ^ 2 + realDot d z ^ 2 := by
    rw [lowerD_quadratic]
    dsimp [s, r, z]
    field_simp [hs0]
  have hproduct : s * realDot d (lowerD.mulVec d) = normSq d * normSq (r - d) := by
    rw [hscaled, normSq_sub r d, realDot_comm r d, ← hdrz]
    ring
  have hD : realDot d (lowerD.mulVec d) ≤ spectralNorm E ^ 2 * normSq d := by
    have hbound := normSq_mulVec_le E witnessX2
    rw [hex] at hbound
    apply (mul_le_mul_iff_right₀ hs).mp
    calc
      s * realDot d (lowerD.mulVec d) = normSq d * normSq (r - d) := hproduct
      _ ≤ normSq d * (spectralNorm E ^ 2 * s) :=
        mul_le_mul_of_nonneg_left hbound (normSq_nonneg d)
      _ = s * (spectralNorm E ^ 2 * normSq d) := by ring
  have hconvex : realDot d (lowerConvexMatrix.mulVec d) ≤ spectralNorm E ^ 2 * normSq d := by
    rw [lowerConvex_quadratic]
    linarith
  have hpositive := lower_convex_gap_positive.dotProduct_mulVec_pos hd
  have hpositive' : 0 < realDot d
      ((lowerConvexMatrix - (99 / 100 : ℝ) • (1 : Mat 4 4)).mulVec d) := by
    simpa only [star_trivial, realDot, dotProduct] using hpositive
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    realDot_sub, realDot_smul, realDot_self] at hpositive'
  apply (mul_lt_mul_iff_right₀ (normSq_pos hd)).mp
  calc
    normSq d * (99 / 100 : ℝ) = (99 / 100 : ℝ) * normSq d := mul_comm _ _
    _ < realDot d (lowerConvexMatrix.mulVec d) := by linarith
    _ ≤ spectralNorm E ^ 2 * normSq d := hconvex
    _ = normSq d * spectralNorm E ^ 2 := mul_comm _ _

theorem witness_backwardError_separation :
    backwardError witnessA witnessB witnessX1 ^ 2 ≤ 1979 / 2000 ∧
    (1979 / 2000 : ℝ) < 99 / 100 ∧
    (99 / 100 : ℝ) < backwardError witnessA witnessB witnessX2 ^ 2 := by
  refine ⟨?_, exact_cutoffs.1, ?_⟩
  · have hb := backwardError_le witnessA witnessB witnessX1 upperPerturbation upper_feasible
    have hbSq := (sq_le_sq₀ (backwardError_nonneg _ _ _) (spectralNorm_nonneg _)).mpr hb
    exact hbSq.trans upperPerturbation_certificate.2.2
  · obtain ⟨E, hE, heq⟩ := (backwardError_isLeast witnessA witnessB witnessX2).1
    rw [heq]
    exact every_second_perturbation_large E hE

#assert_trust kernel every_second_perturbation_large
#assert_trust kernel witness_backwardError_separation
#print axioms every_second_perturbation_large

end NLA.IE17
