/-
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. Apache 2.0; AI-assisted.
Rational rotations require only one exact circle identity and finite coordinates.
-/
import NLA.SP04.Orthogonal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.SP04

@[simp] lemma tuple3_zero {α : Type*} (a b c : α) : (![a,b,c] : Fin 3 → α) 0 = a := rfl
@[simp] lemma tuple3_one {α : Type*} (a b c : α) : (![a,b,c] : Fin 3 → α) 1 = b := rfl
@[simp] lemma tuple3_two {α : Type*} (a b c : α) : (![a,b,c] : Fin 3 → α) 2 = c := rfl

lemma rational_circle (t : ℝ) : rationalCos t ^ 2 + rationalSin t ^ 2 = 1 := by
  have hd : 1 + t ^ 2 ≠ 0 := by positivity
  unfold rationalCos rationalSin
  field_simp
  ring

lemma rotation01_orthogonal (t : ℝ) : Orthogonal (rotation01 t) := by
  have hc := rational_circle t
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotation01, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;>
    nlinarith

lemma rotation02_orthogonal (t : ℝ) : Orthogonal (rotation02 t) := by
  have hc := rational_circle t
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotation02, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;>
    nlinarith

lemma rotation12_orthogonal (t : ℝ) : Orthogonal (rotation12 t) := by
  have hc := rational_circle t
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [rotation12, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_succ] <;>
    nlinarith

theorem rational_rotations_orthogonal (a : Fin 3 → ℝ) :
    Orthogonal (rotations a) :=
  orthogonal_mul _ _ (orthogonal_mul _ _ (rotation01_orthogonal (a 0))
    (rotation02_orthogonal (a 1))) (rotation12_orthogonal (a 2))

lemma rotation01_zero : rotation01 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rotation01, rationalCos, rationalSin]

lemma rotation02_zero : rotation02 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rotation02, rationalCos, rationalSin]

lemma rotation12_zero : rotation12 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rotation12, rationalCos, rationalSin]

lemma rotations_zero : rotations 0 = 1 := by
  simp only [rotations, Pi.zero_apply, rotation01_zero, rotation02_zero, rotation12_zero,
    Matrix.one_mul]

lemma chart_center_value : orthogonalChart chartCenter = Matrix.diagonal centerSingularValues := by
  simp only [orthogonalChart, chartCenter, rotations_zero, Matrix.one_mul,
    Matrix.transpose_one, Matrix.mul_one]

#assert_trust kernel rational_rotations_orthogonal
#print axioms rational_rotations_orthogonal
end NLA.SP04
