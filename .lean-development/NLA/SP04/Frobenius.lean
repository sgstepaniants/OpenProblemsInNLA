/-
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. Apache 2.0; AI-assisted.
The norm in every statement is the explicitly selected actual Frobenius norm.
-/
import NLA.SP04.Definitions
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators
noncomputable section
namespace NLA.SP04

theorem frobenius_norm_squared {n : ℕ} (A : Mat n) :
    0 ≤ frobeniusNorm A ∧ frobeniusNorm A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  letI : NormedAddCommGroup (Mat n) := Matrix.frobeniusNormedAddCommGroup
  have hnorm : frobeniusNorm A = Real.sqrt (∑ i, ∑ j, A i j ^ 2) := by
    change ‖A‖ = _
    simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, Real.sqrt_eq_rpow]
      using Matrix.frobenius_norm_def A
  rw [hnorm]
  exact ⟨Real.sqrt_nonneg _, Real.sq_sqrt
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)⟩

lemma frobenius_norm_sq_trace {n : ℕ} (A : Mat n) :
    frobeniusNorm A ^ 2 = (A.transpose * A).trace := by
  rw [(frobenius_norm_squared A).2]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  simp only [pow_two]

lemma frobenius_diagonal_distance_sq {n : ℕ} (s x : Fin n → ℝ) :
    frobeniusDistance (Matrix.diagonal s) (Matrix.diagonal x) ^ 2 =
      ∑ i, (s i - x i) ^ 2 := by
  rw [frobeniusDistance, (frobenius_norm_squared _).2]
  classical
  simp [Matrix.sub_apply, Matrix.diagonal_apply]

#assert_trust kernel frobenius_norm_squared
#print axioms frobenius_norm_squared
end NLA.SP04
