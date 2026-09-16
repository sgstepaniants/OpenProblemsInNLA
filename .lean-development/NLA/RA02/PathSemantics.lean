/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Chronological list identities hold for every label sequence, including repeats
and zero-probability events. No path independence is assumed.
-/
import NLA.RA02.PivotKernel

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma pathResidual_append {n : ℕ} (A : Square n) (u w : List (Fin n)) :
    pathResidual A (u ++ w) = pathResidual (pathResidual A u) w := by
  induction u generalizing A with
  | nil => rfl
  | cons j u ih =>
      simpa only [List.cons_append, pathResidual] using ih (choleskyStep A j)

lemma pathWeight_append {n : ℕ} (A : Square n) (u w : List (Fin n)) :
    pathWeight A (u ++ w) = pathWeight A u * pathWeight (pathResidual A u) w := by
  induction u generalizing A with
  | nil => simp [pathWeight, pathResidual]
  | cons j u ih =>
      simp only [List.cons_append, pathWeight, pathResidual, ih, mul_assoc]

lemma pathResidual_posSemidef {n : ℕ} (A : Square n) (hA : A.PosSemidef)
    (w : List (Fin n)) : (pathResidual A w).PosSemidef := by
  induction w generalizing A with
  | nil => exact hA
  | cons j w ih =>
      exact ih (choleskyStep A j) (choleskyStep_posSemidef A hA j)

lemma pathWeight_nonneg {n : ℕ} (A : Square n) (hA : A.PosSemidef)
    (w : List (Fin n)) : 0 ≤ pathWeight A w := by
  induction w generalizing A with
  | nil => exact zero_le_one
  | cons j w ih =>
      exact mul_nonneg (pivotMass_nonneg hA j)
        (ih (choleskyStep A j) (choleskyStep_posSemidef A hA j))

lemma pathContribution_nonneg {n : ℕ} (A : Square n) (hA : A.PosSemidef)
    (w : List (Fin n)) : 0 ≤ pathContribution A w := by
  exact mul_nonneg (pathWeight_nonneg A hA w)
    (realTrace_nonneg (pathResidual_posSemidef A hA w))

@[simp] lemma pathResidual_zero {n : ℕ} (w : List (Fin n)) :
    pathResidual (0 : Square n) w = 0 := by
  induction w with
  | nil => rfl
  | cons j w ih => simpa only [pathResidual, choleskyStep_zero] using ih

@[simp] lemma pathContribution_zero {n : ℕ} (w : List (Fin n)) :
    pathContribution (0 : Square n) w = 0 := by
  simp [pathContribution]

lemma pathContribution_cons {n : ℕ} (A : Square n) (j : Fin n) (w : List (Fin n)) :
    pathContribution A (j :: w) = pivotMass A j * pathContribution (choleskyStep A j) w := by
  simp only [pathContribution, pathWeight, pathResidual, mul_assoc]

#print axioms pathResidual_posSemidef
#assert_trust kernel pathResidual_posSemidef
#print axioms pathWeight_append
#assert_trust kernel pathWeight_append
#print axioms pathContribution_nonneg
#assert_trust kernel pathContribution_nonneg

end
end NLA.RA02
