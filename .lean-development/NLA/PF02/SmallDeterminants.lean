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
  fin_cases i <;> fin_cases j
  all_goals
    simp only [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  · change (4 : ℝ) = ((1) * (4) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0))))))
    ring
  · change (2 : ℝ) = ((1) * (2) + ((0) * (3) + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0))))))
    ring
  · change (2 : ℝ) = ((1) * (2) + ((0) * (1) + ((0) * (8/3) + ((0) * (0) + ((0) * (0) + (0) * (0))))))
    ring
  · change (0 : ℝ) = ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (t) + ((0) * (0) + (0) * (0))))))
    ring
  · change (0 : ℝ) = ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + (0) * (0))))))
    ring
  · change (0 : ℝ) = ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (1))))))
    ring
  · change (2 : ℝ) = ((1/2) * (4) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0))))))
    ring
  · change (4 : ℝ) = ((1/2) * (2) + ((1) * (3) + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0))))))
    ring
  · change (2 : ℝ) = ((1/2) * (2) + ((1) * (1) + ((0) * (8/3) + ((0) * (0) + ((0) * (0) + (0) * (0))))))
    ring
  · change (0 : ℝ) = ((1/2) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (t) + ((0) * (0) + (0) * (0))))))
    ring
  · change (0 : ℝ) = ((1/2) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (1) + (0) * (0))))))
    ring
  · change (0 : ℝ) = ((1/2) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (1))))))
    ring
  · change (2 : ℝ) = ((1/2) * (4) + ((1/3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0))))))
    ring
  · change (2 : ℝ) = ((1/2) * (2) + ((1/3) * (3) + ((1) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0))))))
    ring
  · change (4 : ℝ) = ((1/2) * (2) + ((1/3) * (1) + ((1) * (8/3) + ((0) * (0) + ((0) * (0) + (0) * (0))))))
    ring
  · change (0 : ℝ) = ((1/2) * (0) + ((1/3) * (0) + ((1) * (0) + ((0) * (t) + ((0) * (0) + (0) * (0))))))
    ring
  · change (0 : ℝ) = ((1/2) * (0) + ((1/3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (1) + (0) * (0))))))
    ring
  · change (0 : ℝ) = ((1/2) * (0) + ((1/3) * (0) + ((1) * (0) + ((0) * (0) + ((0) * (0) + (0) * (1))))))
    ring
  · change (2 : ℝ) = ((1/2) * (4) + ((1/3) * (0) + ((1/4) * (0) + ((1) * (0) + ((0) * (0) + (0) * (0))))))
    ring
  · change (2 : ℝ) = ((1/2) * (2) + ((1/3) * (3) + ((1/4) * (0) + ((1) * (0) + ((0) * (0) + (0) * (0))))))
    ring
  · change (2 : ℝ) = ((1/2) * (2) + ((1/3) * (1) + ((1/4) * (8/3) + ((1) * (0) + ((0) * (0) + (0) * (0))))))
    ring
  · change (t : ℝ) = ((1/2) * (0) + ((1/3) * (0) + ((1/4) * (0) + ((1) * (t) + ((0) * (0) + (0) * (0))))))
    ring
  · change (0 : ℝ) = ((1/2) * (0) + ((1/3) * (0) + ((1/4) * (0) + ((1) * (0) + ((0) * (1) + (0) * (0))))))
    ring
  · change (0 : ℝ) = ((1/2) * (0) + ((1/3) * (0) + ((1/4) * (0) + ((1) * (0) + ((0) * (0) + (0) * (1))))))
    ring
  · change (2 : ℝ) = ((1/2) * (4) + ((1/3) * (0) + ((1/4) * (0) + ((0) * (0) + ((1) * (0) + (0) * (0))))))
    ring
  · change (2 : ℝ) = ((1/2) * (2) + ((1/3) * (3) + ((1/4) * (0) + ((0) * (0) + ((1) * (0) + (0) * (0))))))
    ring
  · change (2 : ℝ) = ((1/2) * (2) + ((1/3) * (1) + ((1/4) * (8/3) + ((0) * (0) + ((1) * (0) + (0) * (0))))))
    ring
  · change (0 : ℝ) = ((1/2) * (0) + ((1/3) * (0) + ((1/4) * (0) + ((0) * (t) + ((1) * (0) + (0) * (0))))))
    ring
  · change (1 : ℝ) = ((1/2) * (0) + ((1/3) * (0) + ((1/4) * (0) + ((0) * (0) + ((1) * (1) + (0) * (0))))))
    ring
  · change (0 : ℝ) = ((1/2) * (0) + ((1/3) * (0) + ((1/4) * (0) + ((0) * (0) + ((1) * (0) + (0) * (1))))))
    ring
  · change (2 : ℝ) = ((1/2) * (4) + ((1/3) * (0) + ((1/4) * (0) + ((0) * (0) + ((0) * (0) + (1) * (0))))))
    ring
  · change (2 : ℝ) = ((1/2) * (2) + ((1/3) * (3) + ((1/4) * (0) + ((0) * (0) + ((0) * (0) + (1) * (0))))))
    ring
  · change (2 : ℝ) = ((1/2) * (2) + ((1/3) * (1) + ((1/4) * (8/3) + ((0) * (0) + ((0) * (0) + (1) * (0))))))
    ring
  · change (0 : ℝ) = ((1/2) * (0) + ((1/3) * (0) + ((1/4) * (0) + ((0) * (t) + ((0) * (0) + (1) * (0))))))
    ring
  · change (0 : ℝ) = ((1/2) * (0) + ((1/3) * (0) + ((1/4) * (0) + ((0) * (0) + ((0) * (1) + (1) * (0))))))
    ring
  · change (1 : ℝ) = ((1/2) * (0) + ((1/3) * (0) + ((1/4) * (0) + ((0) * (0) + ((0) * (0) + (1) * (1))))))
    ring

private lemma witness_lower_triangular : witnessLower.IsLowerTriangular := by
  intro i j hij
  change i.val < j.val at hij
  fin_cases i <;> fin_cases j
  · exact False.elim ((by decide : ¬ ((0 : ℕ) < 0)) hij)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim ((by decide : ¬ ((1 : ℕ) < 0)) hij)
  · exact False.elim ((by decide : ¬ ((1 : ℕ) < 1)) hij)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim ((by decide : ¬ ((2 : ℕ) < 0)) hij)
  · exact False.elim ((by decide : ¬ ((2 : ℕ) < 1)) hij)
  · exact False.elim ((by decide : ¬ ((2 : ℕ) < 2)) hij)
  · rfl
  · rfl
  · rfl
  · exact False.elim ((by decide : ¬ ((3 : ℕ) < 0)) hij)
  · exact False.elim ((by decide : ¬ ((3 : ℕ) < 1)) hij)
  · exact False.elim ((by decide : ¬ ((3 : ℕ) < 2)) hij)
  · exact False.elim ((by decide : ¬ ((3 : ℕ) < 3)) hij)
  · rfl
  · rfl
  · exact False.elim ((by decide : ¬ ((4 : ℕ) < 0)) hij)
  · exact False.elim ((by decide : ¬ ((4 : ℕ) < 1)) hij)
  · exact False.elim ((by decide : ¬ ((4 : ℕ) < 2)) hij)
  · exact False.elim ((by decide : ¬ ((4 : ℕ) < 3)) hij)
  · exact False.elim ((by decide : ¬ ((4 : ℕ) < 4)) hij)
  · rfl
  · exact False.elim ((by decide : ¬ ((5 : ℕ) < 0)) hij)
  · exact False.elim ((by decide : ¬ ((5 : ℕ) < 1)) hij)
  · exact False.elim ((by decide : ¬ ((5 : ℕ) < 2)) hij)
  · exact False.elim ((by decide : ¬ ((5 : ℕ) < 3)) hij)
  · exact False.elim ((by decide : ¬ ((5 : ℕ) < 4)) hij)
  · exact False.elim ((by decide : ¬ ((5 : ℕ) < 5)) hij)

private lemma witness_upper_triangular (t : ℝ) :
    (witnessUpper t).IsUpperTriangular := by
  intro i j hij
  change j.val < i.val at hij
  fin_cases i <;> fin_cases j
  · exact False.elim ((by decide : ¬ ((0 : ℕ) < 0)) hij)
  · exact False.elim ((by decide : ¬ ((1 : ℕ) < 0)) hij)
  · exact False.elim ((by decide : ¬ ((2 : ℕ) < 0)) hij)
  · exact False.elim ((by decide : ¬ ((3 : ℕ) < 0)) hij)
  · exact False.elim ((by decide : ¬ ((4 : ℕ) < 0)) hij)
  · exact False.elim ((by decide : ¬ ((5 : ℕ) < 0)) hij)
  · rfl
  · exact False.elim ((by decide : ¬ ((1 : ℕ) < 1)) hij)
  · exact False.elim ((by decide : ¬ ((2 : ℕ) < 1)) hij)
  · exact False.elim ((by decide : ¬ ((3 : ℕ) < 1)) hij)
  · exact False.elim ((by decide : ¬ ((4 : ℕ) < 1)) hij)
  · exact False.elim ((by decide : ¬ ((5 : ℕ) < 1)) hij)
  · rfl
  · rfl
  · exact False.elim ((by decide : ¬ ((2 : ℕ) < 2)) hij)
  · exact False.elim ((by decide : ¬ ((3 : ℕ) < 2)) hij)
  · exact False.elim ((by decide : ¬ ((4 : ℕ) < 2)) hij)
  · exact False.elim ((by decide : ¬ ((5 : ℕ) < 2)) hij)
  · rfl
  · rfl
  · rfl
  · exact False.elim ((by decide : ¬ ((3 : ℕ) < 3)) hij)
  · exact False.elim ((by decide : ¬ ((4 : ℕ) < 3)) hij)
  · exact False.elim ((by decide : ¬ ((5 : ℕ) < 3)) hij)
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim ((by decide : ¬ ((4 : ℕ) < 4)) hij)
  · exact False.elim ((by decide : ¬ ((5 : ℕ) < 4)) hij)
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact False.elim ((by decide : ¬ ((5 : ℕ) < 5)) hij)

lemma witness_coordinates_det (t : ℝ) : (witnessCoordinates t).det = 32 * t := by
  rw [witness_coordinates_lu, Matrix.det_mul,
    Matrix.det_of_isLowerTriangular _ witness_lower_triangular,
    Matrix.det_of_isUpperTriangular (witness_upper_triangular t)]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  change ((1 * (1 * (1 * (1 * (1 * (1 * 1)))))) : ℝ) *
    (4 * (3 * ((8/3) * (t * (1 * (1 * 1)))))) = 32 * t
  ring

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
