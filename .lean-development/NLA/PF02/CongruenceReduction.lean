/- Finite coordinate reduction for the actual symmetric congruence action.
Mathematics: Matthew J. Colbrook. Formalization: George Stepaniants, Caltech CMS.
Apache 2.0; AI-assisted. Only degree-two identities are normalized here. -/
import NLA.PF02.Coordinates
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.PF02

/-- Every entry of the genuine six-coordinate action, as a degree-two polynomial.
This matrix is proved equal to the frozen definition; it is not a replacement. -/
def congruencePolynomialMatrix (S : Mat 3) : Mat 6 :=
  !![S 0 0 ^ 2, S 0 1 ^ 2, S 0 2 ^ 2, S 0 0 * S 0 1, S 0 0 * S 0 2, S 0 1 * S 0 2;
     S 1 0 ^ 2, S 1 1 ^ 2, S 1 2 ^ 2, S 1 0 * S 1 1, S 1 0 * S 1 2, S 1 1 * S 1 2;
     S 2 0 ^ 2, S 2 1 ^ 2, S 2 2 ^ 2, S 2 0 * S 2 1, S 2 0 * S 2 2, S 2 1 * S 2 2;
     2 * S 0 0 * S 1 0, 2 * S 0 1 * S 1 1, 2 * S 0 2 * S 1 2, S 0 0 * S 1 1 + S 0 1 * S 1 0, S 0 0 * S 1 2 + S 0 2 * S 1 0, S 0 1 * S 1 2 + S 0 2 * S 1 1;
     2 * S 0 0 * S 2 0, 2 * S 0 1 * S 2 1, 2 * S 0 2 * S 2 2, S 0 0 * S 2 1 + S 0 1 * S 2 0, S 0 0 * S 2 2 + S 0 2 * S 2 0, S 0 1 * S 2 2 + S 0 2 * S 2 1;
     2 * S 1 0 * S 2 0, 2 * S 1 1 * S 2 1, 2 * S 1 2 * S 2 2, S 1 0 * S 2 1 + S 1 1 * S 2 0, S 1 0 * S 2 2 + S 1 2 * S 2 0, S 1 1 * S 2 2 + S 1 2 * S 2 1]

lemma congruence_coordinate_entries (S : Mat 3) :
    congruenceCoordinateMatrix S = congruencePolynomialMatrix S := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    dsimp only [congruenceCoordinateMatrix, congruencePolynomialMatrix,
      symmetricCoordinates, symmetricCoordinateBasis, Matrix.vecCons, Fin.cons] <;>
    simp only [Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;>
    dsimp only [Matrix.vecCons, Fin.cons] <;> ring

private lemma coordinate_basis_symmetric (i : Fin 6) :
    (symmetricCoordinateBasis i).IsSymm := by
  apply Matrix.IsSymm.ext
  intro j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

lemma congruence_coordinate_mul (S T : Mat 3) :
    congruenceCoordinateMatrix (S * T) =
      congruenceCoordinateMatrix S * congruenceCoordinateMatrix T := by
  have hS : ∀ i, (S.transpose * symmetricCoordinateBasis i * S).IsSymm := by
    intro i
    change (S.transpose * symmetricCoordinateBasis i * S).transpose = _
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
      (coordinate_basis_symmetric i).eq, Matrix.mul_assoc]
  calc
    congruenceCoordinateMatrix (S * T) =
        rowCoordinateMatrix (fun i =>
          T.transpose * (S.transpose * symmetricCoordinateBasis i * S) * T) := by
      ext i j
      change symmetricCoordinates
          ((S * T).transpose * symmetricCoordinateBasis i * (S * T)) j =
        symmetricCoordinates
          (T.transpose * (S.transpose * symmetricCoordinateBasis i * S) * T) j
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = congruenceCoordinateMatrix S * congruenceCoordinateMatrix T :=
      rowCoordinates_congruence _ hS T

#assert_trust kernel congruence_coordinate_entries
#print axioms congruence_coordinate_entries
#assert_trust kernel congruence_coordinate_mul
#print axioms congruence_coordinate_mul
end NLA.PF02
