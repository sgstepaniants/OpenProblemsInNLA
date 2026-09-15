/- Colbrook's unchanged exact PF-02 witness.
Formalization: George Stepaniants, Caltech Department of Computing and Mathematical
Sciences. Apache 2.0; AI-assisted. Only exact kernel algebra is used. -/
import NLA.PF02.Coordinates
import NLA.PF02.SmallDeterminants
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.PF02

lemma witness_factor_0_psd : (witnessFactors 0).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro x
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, star_trivial]
    change 0 ≤ (x 0 * (((4) * x 0 + ((0) * x 1 + (0) * x 2))) + (x 1 * (((0) * x 0 + ((2) * x 1 + (0) * x 2))) + x 2 * (((0) * x 0 + ((0) * x 1 + (2) * x 2)))))
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
      sq_nonneg (x 0 + x 2), sq_nonneg (x 0 - x 2),
      sq_nonneg (x 1 + x 2), sq_nonneg (x 1 - x 2)]

lemma witness_factor_1_psd : (witnessFactors 1).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro x
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, star_trivial]
    change 0 ≤ (x 0 * (((2) * x 0 + ((0) * x 1 + (0) * x 2))) + (x 1 * (((0) * x 0 + ((4) * x 1 + (0) * x 2))) + x 2 * (((0) * x 0 + ((0) * x 1 + (2) * x 2)))))
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
      sq_nonneg (x 0 + x 2), sq_nonneg (x 0 - x 2),
      sq_nonneg (x 1 + x 2), sq_nonneg (x 1 - x 2)]

lemma witness_factor_2_psd : (witnessFactors 2).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro x
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, star_trivial]
    change 0 ≤ (x 0 * (((2) * x 0 + ((0) * x 1 + (0) * x 2))) + (x 1 * (((0) * x 0 + ((2) * x 1 + (0) * x 2))) + x 2 * (((0) * x 0 + ((0) * x 1 + (4) * x 2)))))
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
      sq_nonneg (x 0 + x 2), sq_nonneg (x 0 - x 2),
      sq_nonneg (x 1 + x 2), sq_nonneg (x 1 - x 2)]

lemma witness_factor_3_psd : (witnessFactors 3).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro x
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, star_trivial]
    change 0 ≤ (x 0 * (((2) * x 0 + ((1) * x 1 + (0) * x 2))) + (x 1 * (((1) * x 0 + ((2) * x 1 + (0) * x 2))) + x 2 * (((0) * x 0 + ((0) * x 1 + (2) * x 2)))))
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
      sq_nonneg (x 0 + x 2), sq_nonneg (x 0 - x 2),
      sq_nonneg (x 1 + x 2), sq_nonneg (x 1 - x 2)]

lemma witness_factor_4_psd : (witnessFactors 4).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro x
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, star_trivial]
    change 0 ≤ (x 0 * (((2) * x 0 + ((0) * x 1 + (1) * x 2))) + (x 1 * (((0) * x 0 + ((2) * x 1 + (0) * x 2))) + x 2 * (((1) * x 0 + ((0) * x 1 + (2) * x 2)))))
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
      sq_nonneg (x 0 + x 2), sq_nonneg (x 0 - x 2),
      sq_nonneg (x 1 + x 2), sq_nonneg (x 1 - x 2)]

lemma witness_factor_5_psd : (witnessFactors 5).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro x
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, star_trivial]
    change 0 ≤ (x 0 * (((2) * x 0 + ((0) * x 1 + (0) * x 2))) + (x 1 * (((0) * x 0 + ((2) * x 1 + (1) * x 2))) + x 2 * (((0) * x 0 + ((1) * x 1 + (2) * x 2)))))
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
      sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1),
      sq_nonneg (x 0 + x 2), sq_nonneg (x 0 - x 2),
      sq_nonneg (x 1 + x 2), sq_nonneg (x 1 - x 2)]

lemma reflected_factor_three_psd : (reflectedFactors 3).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · apply Matrix.isHermitian_iff_isSymm.mpr
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  · intro x
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Fin.sum_univ_zero, add_zero, star_trivial]
    change 0 ≤ (x 0 * (((2) * x 0 + ((-1) * x 1 + (0) * x 2))) + (x 1 * (((-1) * x 0 + ((2) * x 1 + (0) * x 2))) + x 2 * (((0) * x 0 + ((0) * x 1 + (2) * x 2)))))
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2),
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

/-- One six-coordinate Gram identity covers both reflected orientations. -/
lemma witness_coordinate_gram (t : ℝ) (ht : t ^ 2 = 1) :
    witnessCoordinates t * traceMetric * (witnessCoordinates t).transpose =
      witnessMatrix := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [traceMetric, Matrix.mul_diagonal, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j
  all_goals simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  · change (((4) * 1 * (4) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 24
    nlinarith [ht]
  · change (((4) * 1 * (2) + ((2) * 1 * (4) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 20
    nlinarith [ht]
  · change (((4) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (4) + ((0) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 20
    nlinarith [ht]
  · change (((4) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (t) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((4) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (1) + (0) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((4) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (1)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (4) + ((4) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 20
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((4) * 1 * (4) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 24
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((4) * 1 * (2) + ((2) * 1 * (4) + ((0) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 20
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((4) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (t) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((4) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (1) + (0) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((4) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (1)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (4) + ((2) * 1 * (2) + ((4) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 20
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (4) + ((4) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 20
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((4) * 1 * (4) + ((0) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 24
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((4) * 1 * (2) + ((0) * 2 * (t) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((4) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (1) + (0) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((4) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (1)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (4) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((t) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (4) + ((2) * 1 * (2) + ((t) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (4) + ((t) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((t) * 2 * (t) + ((0) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 14
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((t) * 2 * (0) + ((0) * 2 * (1) + (0) * 2 * (0)))))) : ℝ) = 12
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((t) * 2 * (0) + ((0) * 2 * (0) + (0) * 2 * (1)))))) : ℝ) = 12
    nlinarith [ht]
  · change (((2) * 1 * (4) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((1) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (4) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((1) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (4) + ((0) * 2 * (0) + ((1) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (t) + ((1) * 2 * (0) + (0) * 2 * (0)))))) : ℝ) = 12
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((1) * 2 * (1) + (0) * 2 * (0)))))) : ℝ) = 14
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((1) * 2 * (0) + (0) * 2 * (1)))))) : ℝ) = 12
    nlinarith [ht]
  · change (((2) * 1 * (4) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (0) + (1) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (4) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (0) + (1) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (4) + ((0) * 2 * (0) + ((0) * 2 * (0) + (1) * 2 * (0)))))) : ℝ) = 16
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (t) + ((0) * 2 * (0) + (1) * 2 * (0)))))) : ℝ) = 12
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (1) + (1) * 2 * (0)))))) : ℝ) = 12
    nlinarith [ht]
  · change (((2) * 1 * (2) + ((2) * 1 * (2) + ((2) * 1 * (2) + ((0) * 2 * (0) + ((0) * 2 * (0) + (1) * 2 * (1)))))) : ℝ) = 14
    nlinarith [ht]

lemma witness_factorization : IsPSDFactorization witnessMatrix witnessTuple := by
  refine ⟨witness_factors_psd, witness_factors_psd, ?_⟩
  intro i j
  rw [trace_symmetric_coordinates _ _
    (Matrix.isHermitian_iff_isSymm.mp (witness_factors_psd i).1)
    (Matrix.isHermitian_iff_isSymm.mp (witness_factors_psd j).1)]
  change (∑ r : Fin 6, rowCoordinateMatrix witnessFactors i r * traceWeights r *
    rowCoordinateMatrix witnessFactors j r) = witnessMatrix i j
  rw [witness_coordinates_exact]
  have h := congrFun (congrFun (witness_coordinate_gram (1 : ℝ) (by norm_num)) i) j
  rw [Matrix.mul_apply] at h
  simpa only [traceMetric, Matrix.mul_diagonal, Matrix.transpose_apply] using h

lemma reflected_factorization : IsPSDFactorization witnessMatrix reflectedTuple := by
  refine ⟨reflected_factors_psd, reflected_factors_psd, ?_⟩
  intro i j
  rw [trace_symmetric_coordinates _ _
    (Matrix.isHermitian_iff_isSymm.mp (reflected_factors_psd i).1)
    (Matrix.isHermitian_iff_isSymm.mp (reflected_factors_psd j).1)]
  change (∑ r : Fin 6, rowCoordinateMatrix reflectedFactors i r * traceWeights r *
    rowCoordinateMatrix reflectedFactors j r) = witnessMatrix i j
  rw [reflected_coordinates_exact]
  have h := congrFun (congrFun (witness_coordinate_gram (-1 : ℝ) (by norm_num)) i) j
  rw [Matrix.mul_apply] at h
  simpa only [traceMetric, Matrix.mul_diagonal, Matrix.transpose_apply] using h

theorem witness_orientations :
    orientationDeterminant witnessTuple = 32 ∧
    orientationDeterminant reflectedTuple = -32 := by
  constructor
  · change (rowCoordinateMatrix witnessFactors).det = 32
    rw [witness_coordinates_exact, witness_coordinates_det]
    norm_num
  · change (rowCoordinateMatrix reflectedFactors).det = -32
    rw [reflected_coordinates_exact, witness_coordinates_det]
    norm_num

lemma witness_matrix_det : witnessMatrix.det = 8192 := by
  let F : FactorizationSpace 3 witnessMatrix := ⟨witnessTuple, witness_factorization⟩
  have he := factorization_coordinate_identity witnessMatrix F
  have hU : (rowCoordinateMatrix F.val.1).det = 32 := witness_orientations.1
  have hV : (rowCoordinateMatrix F.val.2).det = 32 := witness_orientations.1
  rw [he, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hU, hV]
  rw [traceMetric, Matrix.det_diagonal]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change (32 : ℝ) * (1 * (1 * (1 * (2 * (2 * (2 * 1)))))) * 32 = 8192
  norm_num

theorem witness_certificates :
    (∀ i j, 0 < witnessMatrix i j) ∧
    IsPSDFactorization witnessMatrix witnessTuple ∧
    IsPSDFactorization witnessMatrix reflectedTuple ∧
    witnessMatrix.det = 8192 ∧ witnessMatrix.rank = 6 := by
  refine ⟨?_, witness_factorization, reflected_factorization, witness_matrix_det, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · change (0 : ℝ) < 24
      norm_num
    · change (0 : ℝ) < 20
      norm_num
    · change (0 : ℝ) < 20
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 20
      norm_num
    · change (0 : ℝ) < 24
      norm_num
    · change (0 : ℝ) < 20
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 20
      norm_num
    · change (0 : ℝ) < 20
      norm_num
    · change (0 : ℝ) < 24
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 14
      norm_num
    · change (0 : ℝ) < 12
      norm_num
    · change (0 : ℝ) < 12
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 12
      norm_num
    · change (0 : ℝ) < 14
      norm_num
    · change (0 : ℝ) < 12
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 16
      norm_num
    · change (0 : ℝ) < 12
      norm_num
    · change (0 : ℝ) < 12
      norm_num
    · change (0 : ℝ) < 14
      norm_num
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
