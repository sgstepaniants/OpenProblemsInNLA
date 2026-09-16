/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original comparison argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Matrix unitary conjugations are connected to Mathlib's genuine C*-norm.
The scoped matrix norm below is exactly the Euclidean operator norm wrapper.
-/
import NLA.MF07.ProductEnvelope
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.LinearAlgebra.UnitaryGroup

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace NLA.MF07

lemma isUnitary_mem {d : ℕ} {Q : Square d} (hQ : IsUnitary Q) :
    Q ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  simpa only [IsUnitary, Unitary.mem_iff, Matrix.star_eq_conjTranspose] using hQ

lemma isUnitary_star {d : ℕ} {Q : Square d} (hQ : IsUnitary Q) :
    IsUnitary Q.conjTranspose := by
  simpa only [IsUnitary, Matrix.conjTranspose_conjTranspose] using And.intro hQ.2 hQ.1

lemma spectralNorm_unitary_left {d : ℕ} {Q : Square d} (hQ : IsUnitary Q) (A : Square d) :
    spectralNorm (Q * A) = spectralNorm A := by
  simpa only [spectralNorm, ← Matrix.cstar_norm_def] using
    CStarRing.norm_mem_unitary_mul A (isUnitary_mem hQ)

lemma spectralNorm_unitary_right {d : ℕ} {Q : Square d} (hQ : IsUnitary Q) (A : Square d) :
    spectralNorm (A * Q) = spectralNorm A := by
  simpa only [spectralNorm, ← Matrix.cstar_norm_def] using
    CStarRing.norm_mul_mem_unitary A (isUnitary_mem hQ)

lemma spectralNorm_unitary_conj {d : ℕ} {Q : Square d} (hQ : IsUnitary Q) (A : Square d) :
    spectralNorm (Q * A * Q.conjTranspose) = spectralNorm A := by
  rw [spectralNorm_unitary_right (isUnitary_star hQ), spectralNorm_unitary_left hQ]

lemma diagonalDamping_apply {d : ℕ} (h : Fin d → ℝ) (X : Square d) (i j : Fin d) :
    diagonalDamping h X i j = (h i : ℂ) * X i j * ((h j)⁻¹ : ℂ) := by
  simp [diagonalDamping, diagonalWeights, inverseDiagonalWeights,
    Matrix.diagonal_mul, Matrix.mul_diagonal]

/-- The diagonal reflection across one coordinate cut. -/
def cutReflection (d k : ℕ) : Square d :=
  Matrix.diagonal (fun i : Fin d => if i.val < k then (1 : ℂ) else -1)

lemma cutReflection_star (d k : ℕ) :
    (cutReflection d k).conjTranspose = cutReflection d k := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < k <;> simp [cutReflection, Matrix.conjTranspose_apply, hi]
  · simp [cutReflection, Matrix.conjTranspose_apply, hij, Ne.symm hij]

lemma cutReflection_unitary (d k : ℕ) : IsUnitary (cutReflection d k) := by
  have hs : cutReflection d k * cutReflection d k = 1 := by
    dsimp only [cutReflection]
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : i.val < k <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hi]
    · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
  exact ⟨by simpa only [cutReflection_star] using hs,
    by simpa only [cutReflection_star] using hs⟩

/-- A convex combination of the identity and reflection-conjugation maps. -/
def cutDamping {d : ℕ} (k : ℕ) (t : ℝ) (X : Square d) : Square d :=
  (((1+t)/2 : ℝ) : ℂ) • X + (((1-t)/2 : ℝ) : ℂ) •
    (cutReflection d k * X * cutReflection d k)

lemma cutDamping_spectralNorm_le {d : ℕ} (k : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (X : Square d) : spectralNorm (cutDamping k t X) ≤ spectralNorm X := by
  have hα : 0 ≤ (1+t)/2 := by linarith
  have hβ : 0 ≤ (1-t)/2 := by linarith
  have hc : spectralNorm (cutReflection d k * X * cutReflection d k) = spectralNorm X := by
    simpa only [cutReflection_star] using
      spectralNorm_unitary_conj (cutReflection_unitary d k) X
  calc
    spectralNorm (cutDamping k t X) ≤
        spectralNorm ((((1+t)/2 : ℝ) : ℂ) • X) +
        spectralNorm ((((1-t)/2 : ℝ) : ℂ) • (cutReflection d k * X * cutReflection d k)) :=
      spectralNorm_add_le _ _
    _ = ((1+t)/2) * spectralNorm X + ((1-t)/2) * spectralNorm X := by
      rw [spectralNorm_smul, spectralNorm_smul, hc]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hα, abs_of_nonneg hβ]
    _ = spectralNorm X := by ring

lemma cutDamping_apply {d : ℕ} (k : ℕ) (t : ℝ) (X : Square d) (i j : Fin d) :
    cutDamping k t X i j =
      (if (i.val < k ↔ j.val < k) then (1 : ℂ) else (t : ℂ)) * X i j := by
  by_cases hi : i.val < k <;> by_cases hj : j.val < k <;>
    simp [cutDamping, cutReflection, Matrix.diagonal_mul, Matrix.mul_diagonal, hi, hj] <;>
    push_cast <;> ring

#print axioms spectralNorm_unitary_conj
#assert_trust kernel spectralNorm_unitary_conj
#print axioms cutDamping_spectralNorm_le
#assert_trust kernel cutDamping_spectralNorm_le

end NLA.MF07
