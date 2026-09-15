/- Exact six-coordinate identities for the actual real symmetric factors.
Mathematics: Matthew J. Colbrook. Formalization: George Stepaniants, Caltech CMS.
Apache 2.0; AI-assisted. No coordinate model replaces a frozen definition. -/
import NLA.PF02.Algebra
import Mathlib.Topology.Instances.Matrix

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.PF02

def traceWeights : Fin 6 → ℝ := ![1, 1, 1, 2, 2, 2]
def traceMetric : Mat 6 := Matrix.diagonal traceWeights

lemma trace_symmetric_coordinates (A B : Mat 3)
    (hA : A.IsSymm) (hB : B.IsSymm) :
    (A * B).trace = ∑ r : Fin 6,
      symmetricCoordinates A r * traceWeights r * symmetricCoordinates B r := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, symmetricCoordinates,
    traceWeights, Fin.sum_univ_succ, hA.apply 0 1, hA.apply 0 2, hA.apply 1 2,
    hB.apply 0 1, hB.apply 0 2, hB.apply 1 2]
  <;> ring

lemma factorization_coordinate_identity (M : Mat 6)
    (F : FactorizationSpace 3 M) :
    M = rowCoordinateMatrix F.val.1 * traceMetric *
      (rowCoordinateMatrix F.val.2).transpose := by
  ext i j
  rw [← F.property.2.2 i j]
  have hA : (F.val.1 i).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp (F.property.1 i).1
  have hB : (F.val.2 j).IsSymm :=
    Matrix.isHermitian_iff_isSymm.mp (F.property.2.1 j).1
  rw [trace_symmetric_coordinates _ _ hA hB]
  simp [Matrix.mul_apply, traceMetric, Matrix.mul_diagonal, rowCoordinateMatrix]

lemma rowCoordinates_congruence (A : Fin 6 → Mat 3)
    (hA : ∀ i, (A i).IsSymm) (S : Mat 3) :
    rowCoordinateMatrix (fun i => S.transpose * A i * S) =
      rowCoordinateMatrix A * congruenceCoordinateMatrix S := by
  ext i j
  fin_cases j <;>
    simp [rowCoordinateMatrix, congruenceCoordinateMatrix, symmetricCoordinates,
      symmetricCoordinateBasis, Matrix.mul_apply, Matrix.transpose_apply,
      Fin.sum_univ_succ, (hA i).apply 0 1, (hA i).apply 0 2, (hA i).apply 1 2] <;> ring

lemma orientation_transform_formula (F : FactorizationSpace 3 witnessMatrix)
    (S : (Mat 3)ˣ) :
    orientationDeterminant (congruenceTransform S (F : FactorTuple 3 6 6)) =
      orientationDeterminant (F : FactorTuple 3 6 6) *
        (congruenceCoordinateMatrix (S : Mat 3)).det := by
  unfold orientationDeterminant
  change (rowCoordinateMatrix (fun i => (S : Mat 3).transpose * F.val.1 i *
    (S : Mat 3))).det = _
  rw [rowCoordinates_congruence F.val.1
    (fun i => Matrix.isHermitian_iff_isSymm.mp (F.property.1 i).1), Matrix.det_mul]

lemma continuous_orientationDeterminant :
    Continuous (fun F : FactorizationSpace 3 witnessMatrix =>
      orientationDeterminant (F : FactorTuple 3 6 6)) := by
  unfold orientationDeterminant
  apply Continuous.matrix_det
  apply continuous_matrix
  intro i j
  fin_cases j <;> dsimp [rowCoordinateMatrix, symmetricCoordinates] <;> fun_prop

#assert_trust kernel trace_symmetric_coordinates
#print axioms trace_symmetric_coordinates
#assert_trust kernel factorization_coordinate_identity
#print axioms factorization_coordinate_identity
#assert_trust kernel rowCoordinates_congruence
#print axioms rowCoordinates_congruence
end NLA.PF02
