/- Fixed-size polynomial certificate for the actual symmetric congruence action.
Mathematics: Matthew J. Colbrook. Formalization: George Stepaniants, Caltech CMS.
Apache 2.0; AI-assisted. All variables remain arbitrary real numbers. -/
import NLA.PF02.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.PF02

/-- Laplace expansion and all concrete finite indices are reduced before ring
normalization. The explicit Matrix.cons_val simproc prevents symbolic tuple
lookups from surviving as spurious polynomial variables.
This is one fixed polynomial identity, including singular S, with no sampled
parameters or external oracle assumption. -/
theorem congruence_coordinate_determinant (S : Mat 3) :
    (congruenceCoordinateMatrix S).det = S.det ^ 4 := by
  simp [congruenceCoordinateMatrix, symmetricCoordinates, symmetricCoordinateBasis,
    Matrix.det_fin_three, Matrix.det_fin_two, Matrix.det_fin_one, Matrix.det_fin_zero,
    Matrix.det_succ_row_zero, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_succ, Matrix.cons_val,
    Fin.succAbove, Fin.lt_def, Fin.ext_iff, Fin.reduceFinMk]
  <;> ring

#assert_trust kernel congruence_coordinate_determinant
#print axioms congruence_coordinate_determinant
end NLA.PF02
