/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Exact LSMR optimization over every vector in the true Krylov spans. The
normal-equation orthogonality is extended from the generators to the entire
subspace and yields the Pythagorean identity used for uniqueness.
-/
import NLA.IE17.ExactData

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical Matrix.Norms.L2Operator
noncomputable section
namespace NLA.IE17

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

def witnessGenerator (j : ℕ) : Vec 3 :=
  ((witnessA.transpose * witnessA) ^ j).mulVec (witnessA.transpose.mulVec witnessB)

theorem witnessGenerator_zero : witnessGenerator 0 = ![11, 6, 5] := by
  simp [witnessGenerator, witnessAt_mulVec, witnessB]

theorem witnessGenerator_one : witnessGenerator 1 = ![11, 216, 125] := by
  norm_num [witnessGenerator, witnessAt_mulVec, witness_gram_mulVec, witnessB]

theorem witnessGenerator_two : witnessGenerator 2 = ![11, 7776, 3125] := by
  ext i
  fin_cases i <;> norm_num [witnessGenerator, witnessA, witnessB, pow_two,
    Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ]

theorem witnessGenerator_mem (k : ℕ) (j : Fin k) :
    witnessGenerator j.val ∈ krylovSpace witnessA witnessB k :=
  Submodule.subset_span ⟨j, rfl⟩

theorem witnessX1_mem : witnessX1 ∈ krylovSpace witnessA witnessB 1 := by
  have hrepr : witnessX1 = (1021 / 31201 : ℝ) • witnessGenerator 0 := by
    rw [witnessGenerator_zero]
    ext i
    fin_cases i <;> norm_num [witnessX1]
  rw [hrepr]
  exact (krylovSpace witnessA witnessB 1).smul_mem _ (witnessGenerator_mem 1 0)

theorem witnessX2_mem : witnessX2 ∈ krylovSpace witnessA witnessB 2 := by
  have hrepr : witnessX2 = (16321 / 110438 : ℝ) • witnessGenerator 0 +
      (-383 / 110438 : ℝ) • witnessGenerator 1 := by
    rw [witnessGenerator_zero, witnessGenerator_one]
    ext i
    fin_cases i <;> norm_num [witnessX2]
  rw [hrepr]
  exact (krylovSpace witnessA witnessB 2).add_mem
    ((krylovSpace witnessA witnessB 2).smul_mem _ (witnessGenerator_mem 2 0))
    ((krylovSpace witnessA witnessB 2).smul_mem _ (witnessGenerator_mem 2 1))

theorem witnessX3_mem : witnessX3 ∈ krylovSpace witnessA witnessB 3 := by
  have hrepr : witnessX3 = (961 / 900 : ℝ) • witnessGenerator 0 +
      (-62 / 900 : ℝ) • witnessGenerator 1 + (1 / 900 : ℝ) • witnessGenerator 2 := by
    rw [witnessGenerator_zero, witnessGenerator_one, witnessGenerator_two]
    ext i
    fin_cases i <;> norm_num [witnessX3]
  rw [hrepr]
  exact (krylovSpace witnessA witnessB 3).add_mem
    ((krylovSpace witnessA witnessB 3).add_mem
      ((krylovSpace witnessA witnessB 3).smul_mem _ (witnessGenerator_mem 3 0))
      ((krylovSpace witnessA witnessB 3).smul_mem _ (witnessGenerator_mem 3 1)))
    ((krylovSpace witnessA witnessB 3).smul_mem _ (witnessGenerator_mem 3 2))

theorem realDot_add_right {n : ℕ} (x y z : Vec n) :
    realDot x (y + z) = realDot x y + realDot x z := by
  simp [realDot, mul_add, Finset.sum_add_distrib]

theorem realDot_smul_right {n : ℕ} (x y : Vec n) (a : ℝ) :
    realDot x (a • y) = a * realDot x y := by
  simp [realDot, Finset.mul_sum, mul_left_comm]

theorem witness_orthogonal_on_krylov (k : ℕ) (z : Vec 3)
    (h : ∀ j : Fin k, realDot (normalResidual witnessA witnessB z)
      ((witnessA.transpose * witnessA).mulVec (witnessGenerator j.val)) = 0) :
    ∀ y ∈ krylovSpace witnessA witnessB k,
      realDot (normalResidual witnessA witnessB z)
        ((witnessA.transpose * witnessA).mulVec y) = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
      rcases hy with ⟨j, rfl⟩
      exact h j
  | zero => simp [realDot]
  | add y v hy hv ihy ihv =>
      simp only [Matrix.mulVec_add, realDot_add_right, ihy, ihv, add_zero]
  | smul a y hy ihy =>
      simp only [Matrix.mulVec_smul, realDot_smul_right, ihy, mul_zero]

theorem witness_pythagorean (y z : Vec 3) :
    normSq (normalResidual witnessA witnessB y) =
      normSq (normalResidual witnessA witnessB z) +
      normSq ((witnessA.transpose * witnessA).mulVec (y - z)) -
      2 * realDot (normalResidual witnessA witnessB z)
        ((witnessA.transpose * witnessA).mulVec (y - z)) := by
  simp [normSq, realDot, witness_normalResidual, witness_gram_mulVec, Fin.sum_univ_succ]
  ring

theorem witness_gram_zero_difference {y z : Vec 3}
    (h : (witnessA.transpose * witnessA).mulVec (y - z) = 0) : y = z := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [witness_gram_mulVec] at h0 h1 h2
  ext i
  fin_cases i
  · change y 0 = z 0
    linarith
  · change y 1 = z 1
    linarith
  · change y 2 = z 2
    linarith

theorem witness_isLSMR_iff_of_orthogonal (k : ℕ) (z : Vec 3)
    (hz : z ∈ krylovSpace witnessA witnessB k)
    (horth : ∀ j : Fin k, realDot (normalResidual witnessA witnessB z)
      ((witnessA.transpose * witnessA).mulVec (witnessGenerator j.val)) = 0) :
    ∀ x : Vec 3, IsLSMRIterate witnessA witnessB k x ↔ x = z := by
  have hpyth : ∀ y ∈ krylovSpace witnessA witnessB k,
      normSq (normalResidual witnessA witnessB y) =
        normSq (normalResidual witnessA witnessB z) +
          normSq ((witnessA.transpose * witnessA).mulVec (y - z)) := by
    intro y hy
    have hd := witness_orthogonal_on_krylov k z horth (y - z)
      ((krylovSpace witnessA witnessB k).sub_mem hy hz)
    rw [witness_pythagorean y z, hd, mul_zero, sub_zero]
  have hmin : ∀ y ∈ krylovSpace witnessA witnessB k,
      euclideanNorm (normalResidual witnessA witnessB z) ≤
        euclideanNorm (normalResidual witnessA witnessB y) := by
    intro y hy
    rw [euclideanNorm_le_iff, hpyth y hy]
    exact le_add_of_nonneg_right (normSq_nonneg _)
  have huniq : ∀ y ∈ krylovSpace witnessA witnessB k,
      euclideanNorm (normalResidual witnessA witnessB y) =
        euclideanNorm (normalResidual witnessA witnessB z) → y = z := by
    intro y hy heq
    have heqSq := congrArg (fun t : ℝ => t ^ 2) heq
    simp only [euclideanNorm_sq] at heqSq
    have hzSq : normSq ((witnessA.transpose * witnessA).mulVec (y - z)) = 0 := by
      linarith [hpyth y hy]
    apply witness_gram_zero_difference
    by_contra hneq
    exact (ne_of_gt (normSq_pos hneq)) hzSq
  intro x
  constructor
  · intro hx
    exact huniq x hx.1 (le_antisymm (hx.2.1 z hz) (hmin x hx.1))
  · rintro rfl
    refine ⟨hz, hmin, ?_⟩
    intro y hy heq
    simpa only [huniq y hy heq]

theorem witness_iterates :
    (∀ x : Vec 3, IsLSMRIterate witnessA witnessB 0 x ↔ x = 0) ∧
    (∀ x : Vec 3, IsLSMRIterate witnessA witnessB 1 x ↔ x = witnessX1) ∧
    (∀ x : Vec 3, IsLSMRIterate witnessA witnessB 2 x ↔ x = witnessX2) ∧
    (∀ x : Vec 3, IsLSMRIterate witnessA witnessB 3 x ↔ x = witnessX3) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply witness_isLSMR_iff_of_orthogonal 0 0 (Submodule.zero_mem _)
    intro j
    exact Fin.elim0 j
  · apply witness_isLSMR_iff_of_orthogonal 1 witnessX1 witnessX1_mem
    intro j
    fin_cases j
    norm_num [witnessGenerator_zero, realDot, witness_normalResidual,
      witness_gram_mulVec, witnessX1, Fin.sum_univ_succ]
  · apply witness_isLSMR_iff_of_orthogonal 2 witnessX2 witnessX2_mem
    intro j
    fin_cases j <;>
      norm_num [witnessGenerator_zero, witnessGenerator_one, realDot,
        witness_normalResidual, witness_gram_mulVec, witnessX2, Fin.sum_univ_succ]
  · apply witness_isLSMR_iff_of_orthogonal 3 witnessX3 witnessX3_mem
    intro j
    rw [witness_before_termination.2.2.2.2.2]
    simp [realDot]

#assert_trust kernel witness_isLSMR_iff_of_orthogonal
#assert_trust kernel witness_iterates
#print axioms witness_iterates

end NLA.IE17
