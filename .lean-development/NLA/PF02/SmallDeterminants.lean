/- Exact triangular certificate for the fixed PF-02 witness coordinates.
Mathematics: Matthew J. Colbrook. Formalization: George Stepaniants, Caltech CMS.
Apache 2.0; AI-assisted. No determinant of size six is expanded. -/
import NLA.PF02.Definitions
import NLA.PF02.FiniteEntries
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.PF02

/-- The one changed coordinate is kept symbolic, covering both signs at once. -/
def witnessCoordinates (t : ℝ) : Mat 6 :=
  !![4, 2, 2, 0, 0, 0;
     2, 4, 2, 0, 0, 0;
     2, 2, 4, 0, 0, 0;
     2, 2, 2, t, 0, 0;
     2, 2, 2, 0, 1, 0;
     2, 2, 2, 0, 0, 1]

private def witnessLower : Mat 6 :=
  !![1, 0, 0, 0, 0, 0;
     1/2, 1, 0, 0, 0, 0;
     1/2, 1/3, 1, 0, 0, 0;
     1/2, 1/3, 1/4, 1, 0, 0;
     1/2, 1/3, 1/4, 0, 1, 0;
     1/2, 1/3, 1/4, 0, 0, 1]

private def witnessUpper (t : ℝ) : Mat 6 :=
  !![4, 2, 2, 0, 0, 0;
     0, 3, 1, 0, 0, 0;
     0, 0, 8/3, 0, 0, 0;
     0, 0, 0, t, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 0, 0, 1]

private lemma witness_coordinates_lu (t : ℝ) :
    witnessCoordinates t = witnessLower * witnessUpper t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      witnessCoordinates, witnessLower, witnessUpper,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
      vector_at_two, vector_at_three, vector_at_four, vector_at_five] <;>
    norm_num <;> ring

private lemma witness_lower_triangular : witnessLower.IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  fin_cases i <;> fin_cases j <;> first | omega | rfl

private lemma witness_upper_triangular (t : ℝ) :
    (witnessUpper t).IsUpperTriangular := by
  intro i j hij
  change j < i at hij
  fin_cases i <;> fin_cases j <;> first | omega | rfl

lemma witness_coordinates_det (t : ℝ) : (witnessCoordinates t).det = 32 * t := by
  rw [witness_coordinates_lu, Matrix.det_mul,
    Matrix.det_of_isLowerTriangular _ witness_lower_triangular,
    Matrix.det_of_isUpperTriangular (witness_upper_triangular t)]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
    witnessLower, witnessUpper, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_succ, vector_at_two, vector_at_three, vector_at_four, vector_at_five]
  norm_num <;> ring

lemma witness_coordinates_exact :
    rowCoordinateMatrix witnessFactors = witnessCoordinates 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

lemma reflected_coordinates_exact :
    rowCoordinateMatrix reflectedFactors = witnessCoordinates (-1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

#assert_trust kernel witness_coordinates_det
#print axioms witness_coordinates_det
end NLA.PF02
