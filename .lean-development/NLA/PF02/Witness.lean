/- Colbrook's unchanged exact PF-02 witness.
Formalization: George Stepaniants, Caltech Department of Computing and Mathematical
Sciences. Apache 2.0; AI-assisted. Only exact kernel algebra is used. -/
import NLA.PF02.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.PF02

lemma witness_factor_0_psd : (witnessFactors 0).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessFactors, reflectedFactors, Matrix.cons_val,
      Fin.ext_iff, Fin.reduceFinMk]
  · intro x
    simp [witnessFactors, reflectedFactors, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
      sq_nonneg (x 0 + x 2), sq_nonneg (x 0 - x 2),
      sq_nonneg (x 1 + x 2), sq_nonneg (x 1 - x 2)]

lemma witness_factor_1_psd : (witnessFactors 1).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessFactors, reflectedFactors, Matrix.cons_val,
      Fin.ext_iff, Fin.reduceFinMk]
  · intro x
    simp [witnessFactors, reflectedFactors, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
      sq_nonneg (x 0 + x 2), sq_nonneg (x 0 - x 2),
      sq_nonneg (x 1 + x 2), sq_nonneg (x 1 - x 2)]

lemma witness_factor_2_psd : (witnessFactors 2).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessFactors, reflectedFactors, Matrix.cons_val,
      Fin.ext_iff, Fin.reduceFinMk]
  · intro x
    simp [witnessFactors, reflectedFactors, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
      sq_nonneg (x 0 + x 2), sq_nonneg (x 0 - x 2),
      sq_nonneg (x 1 + x 2), sq_nonneg (x 1 - x 2)]

lemma witness_factor_3_psd : (witnessFactors 3).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessFactors, reflectedFactors, Matrix.cons_val,
      Fin.ext_iff, Fin.reduceFinMk]
  · intro x
    simp [witnessFactors, reflectedFactors, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
      sq_nonneg (x 0 + x 2), sq_nonneg (x 0 - x 2),
      sq_nonneg (x 1 + x 2), sq_nonneg (x 1 - x 2)]

lemma witness_factor_4_psd : (witnessFactors 4).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessFactors, reflectedFactors, Matrix.cons_val,
      Fin.ext_iff, Fin.reduceFinMk]
  · intro x
    simp [witnessFactors, reflectedFactors, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
      sq_nonneg (x 0 + x 2), sq_nonneg (x 0 - x 2),
      sq_nonneg (x 1 + x 2), sq_nonneg (x 1 - x 2)]

lemma witness_factor_5_psd : (witnessFactors 5).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessFactors, reflectedFactors, Matrix.cons_val,
      Fin.ext_iff, Fin.reduceFinMk]
  · intro x
    simp [witnessFactors, reflectedFactors, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
      sq_nonneg (x 0 + x 2), sq_nonneg (x 0 - x 2),
      sq_nonneg (x 1 + x 2), sq_nonneg (x 1 - x 2)]

lemma reflected_factor_three_psd : (reflectedFactors 3).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.IsHermitian.ext
    intro i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessFactors, reflectedFactors, Matrix.cons_val,
      Fin.ext_iff, Fin.reduceFinMk]
  · intro x
    simp [witnessFactors, reflectedFactors, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    <;> nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
      sq_nonneg (x 0 + x 2), sq_nonneg (x 0 - x 2),
      sq_nonneg (x 1 + x 2), sq_nonneg (x 1 - x 2)]

lemma witness_factors_psd (i : Fin 6) : (witnessFactors i).PosSemidef := by
  fin_cases i
  · exact witness_factor_0_psd
  · exact witness_factor_1_psd
  · exact witness_factor_2_psd
  · exact witness_factor_3_psd
  · exact witness_factor_4_psd
  · exact witness_factor_5_psd

lemma reflected_factors_psd (i : Fin 6) : (reflectedFactors i).PosSemidef := by
  by_cases hi : i = 3
  · subst i
    exact reflected_factor_three_psd
  · simpa [reflectedFactors, hi] using witness_factors_psd i

lemma witness_factorization : IsPSDFactorization witnessMatrix witnessTuple := by
  refine ⟨witness_factors_psd, witness_factors_psd, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessTuple, witnessFactors, witnessMatrix,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val, Fin.ext_iff, Fin.reduceFinMk]

lemma reflected_factorization : IsPSDFactorization witnessMatrix reflectedTuple := by
  refine ⟨reflected_factors_psd, reflected_factors_psd, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [reflectedTuple, reflectedFactors, witnessFactors, witnessMatrix,
      Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val, Fin.ext_iff, Fin.reduceFinMk]

theorem witness_orientations :
    orientationDeterminant witnessTuple = 32 ∧
    orientationDeterminant reflectedTuple = -32 := by
  constructor <;>
    norm_num [orientationDeterminant, rowCoordinateMatrix, symmetricCoordinates,
      witnessTuple, reflectedTuple, witnessFactors, reflectedFactors,
      Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
      Matrix.det_fin_one, Matrix.det_fin_zero, Matrix.submatrix_apply,
      Fin.sum_univ_succ, Matrix.cons_val, Fin.succAbove, Fin.lt_def,
      Fin.ext_iff, Fin.reduceFinMk]

lemma witness_matrix_det : witnessMatrix.det = 8192 := by
  let U : Mat 6 := rowCoordinateMatrix witnessFactors
  let G : Mat 6 := Matrix.diagonal (![1, 1, 1, 2, 2, 2] : Fin 6 → ℝ)
  have hU : U.det = 32 := witness_orientations.1
  have he : witnessMatrix = U * G * U.transpose := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [U, G, rowCoordinateMatrix, symmetricCoordinates, witnessFactors,
        witnessMatrix, Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ,
        Matrix.cons_val, Fin.ext_iff, Fin.reduceFinMk]
  rw [he, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hU]
  norm_num [G, Matrix.det_diagonal, Fin.prod_univ_succ, Matrix.cons_val]

theorem witness_certificates :
    (∀ i j, 0 < witnessMatrix i j) ∧
    IsPSDFactorization witnessMatrix witnessTuple ∧
    IsPSDFactorization witnessMatrix reflectedTuple ∧
    witnessMatrix.det = 8192 ∧ witnessMatrix.rank = 6 := by
  refine ⟨?_, witness_factorization, reflected_factorization, witness_matrix_det, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [witnessMatrix]
  · have hne : witnessMatrix.det ≠ 0 := by rw [witness_matrix_det]; norm_num
    simpa using Matrix.rank_of_det_ne_zero hne

#assert_trust kernel witness_factorization
#print axioms witness_factorization
#assert_trust kernel reflected_factorization
#print axioms reflected_factorization
#assert_trust kernel witness_orientations
#print axioms witness_orientations
#assert_trust kernel witness_certificates
#print axioms witness_certificates
end NLA.PF02
