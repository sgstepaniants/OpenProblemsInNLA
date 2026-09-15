/-
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. Apache 2.0; AI-assisted.
Differentiability uses the genuine finite product norm, with entrywise bilinear maps.
No submultiplicative property of the matrix entry sup norm is assumed.
-/
import NLA.SP04.Rotations
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option leancert.trust "kernel"
open scoped BigOperators
noncomputable section
namespace NLA.SP04

@[fun_prop] lemma contDiff_matrix_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (A B : E → Mat n) (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B) :
    ContDiff ℝ 1 (fun x => A x * B x) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ 1 (fun x => ∑ k : Fin n, A x i k * B x k j)
  apply ContDiff.sum
  intro k hk
  exact (contDiff_pi.mp (contDiff_pi.mp hA i) k).mul
    (contDiff_pi.mp (contDiff_pi.mp hB k) j)

@[fun_prop] lemma contDiff_matrix_transpose {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (A : E → Mat n) (hA : ContDiff ℝ 1 A) :
    ContDiff ℝ 1 (fun x => (A x).transpose) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiff_pi.mp (contDiff_pi.mp hA j) i

@[fun_prop] lemma contDiff_matrix_diagonal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (a : E → Fin n → ℝ) (ha : ContDiff ℝ 1 a) :
    ContDiff ℝ 1 (fun x => Matrix.diagonal (a x)) := by
  classical
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  by_cases hij : i = j
  · subst j
    simpa only [Matrix.diagonal_apply_eq] using contDiff_pi.mp ha i
  · simpa only [Matrix.diagonal_apply_ne _ hij] using
      (contDiff_const : ContDiff ℝ 1 (fun _ : E => (0 : ℝ)))

@[fun_prop] lemma rationalCos_contDiff : ContDiff ℝ 1 rationalCos := by
  unfold rationalCos
  fun_prop (disch := positivity)

@[fun_prop] lemma rationalSin_contDiff : ContDiff ℝ 1 rationalSin := by
  unfold rationalSin
  fun_prop (disch := positivity)

@[fun_prop] lemma rotation01_contDiff : ContDiff ℝ 1 rotation01 := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [rotation01, Matrix.of_apply, tuple3_zero, tuple3_one, tuple3_two] <;> fun_prop

@[fun_prop] lemma rotation02_contDiff : ContDiff ℝ 1 rotation02 := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [rotation02, Matrix.of_apply, tuple3_zero, tuple3_one, tuple3_two] <;> fun_prop

@[fun_prop] lemma rotation12_contDiff : ContDiff ℝ 1 rotation12 := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  fin_cases i <;> fin_cases j <;>
    simp only [rotation12, Matrix.of_apply, tuple3_zero, tuple3_one, tuple3_two] <;> fun_prop

@[fun_prop] lemma rotations_contDiff : ContDiff ℝ 1 rotations := by
  unfold rotations
  apply contDiff_matrix_mul
  · apply contDiff_matrix_mul
    · exact rotation01_contDiff.comp (contDiff_apply ℝ ℝ (0 : Fin 3))
    · exact rotation02_contDiff.comp (contDiff_apply ℝ ℝ (1 : Fin 3))
  · exact rotation12_contDiff.comp (contDiff_apply ℝ ℝ (2 : Fin 3))

lemma orthogonal_chart_contDiff : ContDiff ℝ 1 orthogonalChart := by
  unfold orthogonalChart
  apply contDiff_matrix_mul
  · apply contDiff_matrix_mul
    · exact rotations_contDiff.comp (by fun_prop)
    · apply contDiff_matrix_diagonal
      fun_prop
  · apply contDiff_matrix_transpose
    exact rotations_contDiff.comp (by fun_prop)

#assert_trust kernel orthogonal_chart_contDiff
#print axioms orthogonal_chart_contDiff
end NLA.SP04
