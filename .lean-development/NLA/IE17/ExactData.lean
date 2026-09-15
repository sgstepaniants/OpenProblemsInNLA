/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact small-dimensional witness arithmetic. All constants below are rational;
no search, floating-point recurrence, or interval subdivision is required.
-/
import NLA.IE17.Geometry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical Matrix.Norms.L2Operator
noncomputable section
namespace NLA.IE17

theorem witnessA_mulVec (x : Vec 3) :
    witnessA.mulVec x = ![x 0, 6 * x 1, 5 * x 2, 0] := by
  ext i
  fin_cases i <;> simp [witnessA, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem witnessAt_mulVec (y : Vec 4) :
    witnessA.transpose.mulVec y = ![y 0, 6 * y 1, 5 * y 2] := by
  ext i
  fin_cases i <;> simp [witnessA, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem witness_gram : witnessA.transpose * witnessA = !![1,0,0; 0,36,0; 0,0,25] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, Matrix.mul_apply, Fin.sum_univ_succ]

theorem witness_gram_mulVec (x : Vec 3) :
    (witnessA.transpose * witnessA).mulVec x = ![x 0, 36 * x 1, 25 * x 2] := by
  rw [witness_gram]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem witness_full_column_rank : witnessA.rank = 3 := by
  rw [← Matrix.rank_transpose_mul_self, witness_gram]
  have hdet : ( !![1,0,0; 0,36,0; 0,0,25] : Mat 3 3).det ≠ 0 := by
    norm_num [Matrix.det_fin_three]
  simpa using Matrix.rank_of_det_ne_zero hdet

theorem witness_normalResidual (x : Vec 3) :
    normalResidual witnessA witnessB x = ![11 - x 0, 6 - 36 * x 1, 5 - 25 * x 2] := by
  unfold normalResidual residual
  rw [witnessA_mulVec, witnessAt_mulVec]
  ext i
  fin_cases i <;> simp [witnessB] <;> ring

theorem witness_residual_one :
    residual witnessA witnessB witnessX1 =
      (1 / 31201 : ℝ) • ![331980, -5555, 5676, 31201] := by
  unfold residual
  rw [witnessA_mulVec]
  ext i
  fin_cases i <;> norm_num [witnessB, witnessX1]

theorem witness_residual_two :
    residual witnessA witnessB witnessX2 =
      (1 / 55219 : ℝ) • ![519750, 9625, -29106, 55219] := by
  unfold residual
  rw [witnessA_mulVec]
  ext i
  fin_cases i <;> norm_num [witnessB, witnessX2]

theorem witness_squared_lengths :
    normSq witnessX1 = 189724262 / 973502401 ∧
    normSq (residual witnessA witnessB witnessX1) = 111247297802 / 973502401 ∧
    normSq witnessX2 = 8026273307 / 3049137961 ∧
    normSq (residual witnessA witnessB witnessX2) = 274129000322 / 3049137961 := by
  rw [witness_residual_one, witness_residual_two]
  norm_num [normSq, witnessX1, witnessX2, Fin.sum_univ_succ]

theorem witness_before_termination :
    witnessX1 ≠ 0 ∧ witnessX2 ≠ 0 ∧
    normalResidual witnessA witnessB 0 ≠ 0 ∧
    normalResidual witnessA witnessB witnessX1 ≠ 0 ∧
    normalResidual witnessA witnessB witnessX2 ≠ 0 ∧
    normalResidual witnessA witnessB witnessX3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    norm_num [witnessX1] at h0
  · intro h
    have h0 := congrFun h 0
    norm_num [witnessX2] at h0
  · intro h
    have h0 := congrFun h 0
    norm_num [witness_normalResidual] at h0
  · intro h
    have h0 := congrFun h 0
    norm_num [witness_normalResidual, witnessX1] at h0
  · intro h
    have h0 := congrFun h 0
    norm_num [witness_normalResidual, witnessX2] at h0
  · rw [witness_normalResidual]
    ext i
    fin_cases i <;> norm_num [witnessX3]

theorem witness_residuals_nonzero :
    residual witnessA witnessB witnessX1 ≠ 0 ∧
    residual witnessA witnessB witnessX2 ≠ 0 := by
  constructor <;> intro h
  · have h3 := congrFun h 3
    norm_num [witness_residual_one] at h3
  · have h3 := congrFun h 3
    norm_num [witness_residual_two] at h3

theorem witness_normalResidual_injective :
    Function.Injective (normalResidual witnessA witnessB) := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [witness_normalResidual] at h0 h1 h2
  ext i
  fin_cases i <;> linarith

theorem exact_cutoffs :
    (1979 / 2000 : ℝ) < 99 / 100 ∧
    (69694107852573439503892031925 / 69323394392991282508138323472 : ℝ) < 503 / 500 ∧
    (503 / 500 : ℝ) < 1007 / 1000 ∧
    (1007 / 1000 : ℝ) < 5430772101137459612205263871781350 /
      5387955615790281743396033884265233 := by
  norm_num

#assert_trust kernel witness_full_column_rank
#assert_trust kernel witness_before_termination
#assert_trust kernel exact_cutoffs

end NLA.IE17
