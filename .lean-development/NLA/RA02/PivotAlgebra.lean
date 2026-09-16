/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

One rank-one congruence proves preservation of actual complex PSD. The
calculation uses matrix rank-one identities, not expanded double sums.
-/
import NLA.RA02.Definitions
import Mathlib.Tactic
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

/-- Ordinary column elimination, before the matching left congruence. -/
def pivotEliminator {n : ℕ} (A : Square n) (j : Fin n) : Square n :=
  1 - Matrix.vecMulVec (Pi.single j 1) (fun b => A j b / A j j)

lemma choleskyStep_pivot_row {n : ℕ} (A : Square n) (j : Fin n)
    (hj : A j j ≠ 0) (b : Fin n) : choleskyStep A j j b = 0 := by
  simp only [choleskyStep, hj, ↓reduceIte]
  field_simp [hj] <;> ring

lemma choleskyStep_pivot_col {n : ℕ} (A : Square n) (j : Fin n)
    (hj : A j j ≠ 0) (a : Fin n) : choleskyStep A j a j = 0 := by
  simp only [choleskyStep, hj, ↓reduceIte]
  field_simp [hj] <;> ring

lemma choleskyStep_preserves_zero_row {n : ℕ} (A : Square n) (i j : Fin n)
    (hi : ∀ b, A i b = 0) : ∀ b, choleskyStep A j i b = 0 := by
  intro b
  by_cases hj : A j j = 0 <;> simp [choleskyStep, hj, hi]

lemma choleskyStep_preserves_zero_col {n : ℕ} (A : Square n) (i j : Fin n)
    (hi : ∀ a, A a i = 0) : ∀ a, choleskyStep A j a i = 0 := by
  intro a
  by_cases hj : A j j = 0 <;> simp [choleskyStep, hj, hi]

@[simp] lemma choleskyStep_zero {n : ℕ} (j : Fin n) :
    choleskyStep (0 : Square n) j = 0 := by
  simp [choleskyStep]

lemma mul_pivotEliminator {n : ℕ} (A : Square n) (j : Fin n)
    (hj : A j j ≠ 0) : A * pivotEliminator A j = choleskyStep A j := by
  rw [pivotEliminator, mul_sub, mul_one, Matrix.mul_vecMulVec,
    Matrix.mulVec_single_one]
  ext a b
  simp only [Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.col_apply,
    choleskyStep, hj, ↓reduceIte]
  ring

lemma conjTranspose_pivotEliminator_mul_step {n : ℕ} (A : Square n) (j : Fin n)
    (hj : A j j ≠ 0) :
    (pivotEliminator A j)ᴴ * choleskyStep A j = choleskyStep A j := by
  have he : star (Pi.single j (1 : ℂ) : Fin n → ℂ) =
      (Pi.single j 1 : Fin n → ℂ) := by
    ext a
    simp [Pi.single_apply]
  have hrow : star (Pi.single j (1 : ℂ) : Fin n → ℂ) ᵥ* choleskyStep A j = 0 := by
    rw [he, Matrix.single_one_vecMul]
    ext b
    exact choleskyStep_pivot_row A j hj b
  rw [pivotEliminator, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_vecMulVec, sub_mul, one_mul, Matrix.vecMulVec_mul, hrow]
  simp

lemma choleskyStep_eq_congruence {n : ℕ} (A : Square n) (j : Fin n)
    (hj : A j j ≠ 0) :
    choleskyStep A j = (pivotEliminator A j)ᴴ * A * pivotEliminator A j := by
  rw [Matrix.mul_assoc, mul_pivotEliminator A j hj,
    conjTranspose_pivotEliminator_mul_step A j hj]

lemma choleskyStep_posSemidef {n : ℕ} (A : Square n) (hA : A.PosSemidef)
    (j : Fin n) : (choleskyStep A j).PosSemidef := by
  by_cases hj : A j j = 0
  · simpa only [choleskyStep, hj, ↓reduceIte] using hA
  · rw [choleskyStep_eq_congruence A j hj]
    exact hA.conjTranspose_mul_mul_same (pivotEliminator A j)

#print axioms choleskyStep_eq_congruence
#assert_trust kernel choleskyStep_eq_congruence
#print axioms choleskyStep_posSemidef
#assert_trust kernel choleskyStep_posSemidef

end
end NLA.RA02
