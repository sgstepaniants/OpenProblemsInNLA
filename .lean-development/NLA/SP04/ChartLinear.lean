/-
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. Apache 2.0; AI-assisted.
The inverse certificate consists of three explicit two-by-two rational blocks.
-/
import NLA.SP04.Rotations
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.SP04

/-- Inverses of the three off-diagonal blocks of the frozen derivative formula. -/
def chartDerivativeInverse (A : Mat 3) : Parameters :=
  (![A 0 0, A 1 1, A 2 2],
   ![(219375 * A 0 1 + 218875 * A 1 0) / 3506,
     (43975 * A 0 2 + 43775 * A 2 0) / 1404,
     (219875 * A 1 2 + 219375 * A 2 1) / 3514],
   ![(218875 * A 0 1 + 219375 * A 1 0) / 3506,
     (43775 * A 0 2 + 43975 * A 2 0) / 1404,
     (219375 * A 1 2 + 219875 * A 2 1) / 3514])

lemma chartDerivative_add (h k : Parameters) :
    chartDerivativeFormula centerSingularValues (h + k) =
      chartDerivativeFormula centerSingularValues h + chartDerivativeFormula centerSingularValues k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartDerivativeFormula, Matrix.add_apply] <;> ring

lemma chartDerivative_smul (r : ℝ) (h : Parameters) :
    chartDerivativeFormula centerSingularValues (r • h) =
      r • chartDerivativeFormula centerSingularValues h := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartDerivativeFormula, Matrix.smul_apply, smul_eq_mul] <;> ring

lemma chartDerivative_left_inverse (h : Parameters) :
    chartDerivativeInverse (chartDerivativeFormula centerSingularValues h) = h := by
  apply Prod.ext
  · funext i
    fin_cases i <;> simp [chartDerivativeInverse, chartDerivativeFormula]
  · apply Prod.ext
    · funext i
      fin_cases i <;>
        norm_num [chartDerivativeInverse, chartDerivativeFormula, centerSingularValues] <;> ring
    · funext i
      fin_cases i <;>
        norm_num [chartDerivativeInverse, chartDerivativeFormula, centerSingularValues] <;> ring

lemma chartDerivative_right_inverse (A : Mat 3) :
    chartDerivativeFormula centerSingularValues (chartDerivativeInverse A) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [chartDerivativeInverse, chartDerivativeFormula, centerSingularValues] <;> ring

/-- The complete nine-dimensional linear bijection, with its inverse proved entrywise. -/
def chartLinearEquiv : Parameters ≃ₗ[ℝ] Mat 3 where
  toFun := chartDerivativeFormula centerSingularValues
  invFun := chartDerivativeInverse
  left_inv := chartDerivative_left_inverse
  right_inv := chartDerivative_right_inverse
  map_add' := chartDerivative_add
  map_smul' := chartDerivative_smul

/-- Finite dimensionality proves continuity of both actual linear maps. -/
def chartContinuousLinearEquiv : Parameters ≃L[ℝ] Mat 3 :=
  chartLinearEquiv.toContinuousLinearEquiv

lemma chartContinuousLinearEquiv_apply (h : Parameters) :
    chartContinuousLinearEquiv h = chartDerivativeFormula centerSingularValues h := rfl

#assert_trust kernel chartDerivative_left_inverse
#assert_trust kernel chartDerivative_right_inverse
#print axioms chartDerivative_left_inverse
#print axioms chartDerivative_right_inverse
end NLA.SP04
