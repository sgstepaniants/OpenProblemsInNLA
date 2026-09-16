/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Exact finite head/tail reindexing proves full normalization and the conditional
expectation recursion. The sample space contains every ordered label history.
-/
import NLA.RA02.PathSemantics
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma sum_histories_succ (n k : ℕ) (F : History n (k + 1) → ℝ) :
    (∑ f : History n (k + 1), F f) =
      ∑ j : Fin n, ∑ f : History n k, F (Fin.cons j f) := by
  classical
  calc
    (∑ f : History n (k + 1), F f) =
        ∑ p : Fin n × History n k, F (Fin.cons p.1 p.2) := by
      symm
      exact Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (k + 1) => Fin n))
        (fun p => F (Fin.cons p.1 p.2)) F (fun _ => rfl)
    _ = ∑ j : Fin n, ∑ f : History n k, F (Fin.cons j f) :=
      Fintype.sum_prod_type _

lemma sum_pathWeight (n : ℕ) (hn : 1 ≤ n) (A : Square n) (hA : A.PosSemidef)
    (k : ℕ) : (∑ f : History n k, pathWeight A (List.ofFn f)) = 1 := by
  classical
  induction k generalizing A with
  | zero => simp [pathWeight]
  | succ k ih =>
      rw [sum_histories_succ]
      simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, pathWeight]
      calc
        (∑ j : Fin n, ∑ f : History n k,
            pivotMass A j * pathWeight (choleskyStep A j) (List.ofFn f)) =
            ∑ j : Fin n, pivotMass A j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [← Finset.mul_sum, ih (choleskyStep A j)
            (choleskyStep_posSemidef A hA j), mul_one]
        _ = 1 := sum_pivotMass n hn A

theorem finite_path_law (n : ℕ) (hn : 1 ≤ n) (A : Square n) (hA : A.PosSemidef) :
    (∀ k : ℕ,
      (∀ f : History n k, 0 ≤ pathWeight A (List.ofFn f) ∧
        (pathResidual A (List.ofFn f)).PosSemidef) ∧
      (∑ f : History n k, pathWeight A (List.ofFn f)) = 1) ∧
    ∀ (w : List (Fin n)) (j : Fin n),
      pathResidual A (w ++ [j]) = choleskyStep (pathResidual A w) j ∧
      pathWeight A (w ++ [j]) = pathWeight A w * pivotMass (pathResidual A w) j := by
  refine ⟨?_, ?_⟩
  · intro k
    exact ⟨fun f => ⟨pathWeight_nonneg A hA (List.ofFn f),
      pathResidual_posSemidef A hA (List.ofFn f)⟩, sum_pathWeight n hn A hA k⟩
  · intro w j
    constructor
    · simpa only [pathResidual] using pathResidual_append A w [j]
    · simpa only [pathWeight, mul_one] using pathWeight_append A w [j]

@[simp] lemma expectedTrace_zero_steps {n : ℕ} (A : Square n) :
    expectedTrace A 0 = realTrace A := by
  classical
  simp [expectedTrace, pathContribution, pathWeight, pathResidual]

lemma expectedTrace_nonneg {n : ℕ} (A : Square n) (hA : A.PosSemidef) (k : ℕ) :
    0 ≤ expectedTrace A k := by
  exact Finset.sum_nonneg (fun f _ => pathContribution_nonneg A hA (List.ofFn f))

theorem zero_residual (n k : ℕ) (w : List (Fin n)) :
    pathResidual (0 : Square n) w = 0 ∧ expectedTrace (0 : Square n) k = 0 := by
  refine ⟨pathResidual_zero w, ?_⟩
  simp [expectedTrace]

lemma expectedTrace_succ {n : ℕ} (A : Square n) (k : ℕ) :
    expectedTrace A (k + 1) =
      ∑ j : Fin n, pivotMass A j * expectedTrace (choleskyStep A j) k := by
  classical
  unfold expectedTrace
  rw [sum_histories_succ]
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, pathContribution_cons,
    Finset.mul_sum]

theorem expected_trace_recursion (n : ℕ) (hn : 1 ≤ n) (A : Square n)
    (hA : A.PosSemidef) (k : ℕ) :
    expectedTrace A 0 = realTrace A ∧ 0 ≤ expectedTrace A k ∧
    expectedTrace A (k + 1) =
      ∑ j : Fin n, pivotMass A j * expectedTrace (choleskyStep A j) k := by
  exact ⟨expectedTrace_zero_steps A, expectedTrace_nonneg A hA k, expectedTrace_succ A k⟩

#print axioms finite_path_law
#assert_trust kernel finite_path_law
#print axioms zero_residual
#assert_trust kernel zero_residual
#print axioms expected_trace_recursion
#assert_trust kernel expected_trace_recursion

end
end NLA.RA02
