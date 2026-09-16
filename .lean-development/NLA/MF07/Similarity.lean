/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original comparison:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Explicit similarity identities and operator-norm bounds. The matrix norm is
always the actual complex Euclidean operator norm.
-/
import NLA.MF07.CappedWeights

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace NLA.MF07

lemma rotatedGenerator_apply {d : ℕ} (Q : Square d) (σ : Fin d → ℝ)
    (A : Square d) (i j : Fin d) :
    rotatedGenerator Q σ A i j =
      ((σ i)⁻¹ : ℂ) * (Q.conjTranspose * A * Q) i j * (σ j : ℂ) := by
  have he : rotatedGenerator Q σ A =
      inverseDiagonalWeights σ * (Q.conjTranspose * A * Q) * diagonalWeights σ := by
    dsimp [rotatedGenerator]
    noncomm_ring
  rw [he]
  simp [diagonalWeights, inverseDiagonalWeights, Matrix.diagonal_mul, Matrix.mul_diagonal]

lemma rotatedGenerator_change_weights {d : ℕ} (Q : Square d) (σ τ : Fin d → ℝ)
    (hσ : ∀ i, σ i ≠ 0) (hτ : ∀ i, τ i ≠ 0) (A : Square d) :
    diagonalDamping (fun i => σ i / τ i) (rotatedGenerator Q σ A) =
      rotatedGenerator Q τ A := by
  ext i j
  rw [diagonalDamping_apply, rotatedGenerator_apply, rotatedGenerator_apply]
  have hσc : ∀ k, (σ k : ℂ) ≠ 0 := fun k => Complex.ofReal_ne_zero.mpr (hσ k)
  have hτc : ∀ k, (τ k : ℂ) ≠ 0 := fun k => Complex.ofReal_ne_zero.mpr (hτ k)
  push_cast
  field_simp [hσc i, hσc j, hτc i, hτc j]
  <;> ring

lemma similarity_inverse_pairs {d : ℕ} {Q : Square d} (hQ : IsUnitary Q)
    (σ : Fin d → ℝ) (hσ : ∀ i, σ i ≠ 0) :
    (Q * diagonalWeights σ) * (inverseDiagonalWeights σ * Q.conjTranspose) = 1 ∧
      (inverseDiagonalWeights σ * Q.conjTranspose) * (Q * diagonalWeights σ) = 1 := by
  have hi := diagonal_inverse σ hσ
  constructor
  · calc
      _ = Q * (diagonalWeights σ * inverseDiagonalWeights σ) * Q.conjTranspose := by
        noncomm_ring
      _ = 1 := by rw [hi.1, mul_one, hQ.2]
  · calc
      _ = inverseDiagonalWeights σ * (Q.conjTranspose * Q) * diagonalWeights σ := by
        noncomm_ring
      _ = 1 := by rw [hQ.1, mul_one, hi.2]

lemma rotatedGenerator_one {d : ℕ} {Q : Square d} (hQ : IsUnitary Q)
    (σ : Fin d → ℝ) (hσ : ∀ i, σ i ≠ 0) :
    rotatedGenerator Q σ (1 : Square d) = 1 := by
  calc
    _ = (inverseDiagonalWeights σ * Q.conjTranspose) * (Q * diagonalWeights σ) := by
      dsimp [rotatedGenerator]
      noncomm_ring
    _ = 1 := (similarity_inverse_pairs hQ σ hσ).2

lemma rotatedGenerator_mul {d : ℕ} {Q : Square d} (hQ : IsUnitary Q)
    (σ : Fin d → ℝ) (hσ : ∀ i, σ i ≠ 0) (A B : Square d) :
    rotatedGenerator Q σ (A * B) = rotatedGenerator Q σ A * rotatedGenerator Q σ B := by
  have hi := (similarity_inverse_pairs hQ σ hσ).1
  symm
  calc
    _ = inverseDiagonalWeights σ * Q.conjTranspose * A *
        ((Q * diagonalWeights σ) * (inverseDiagonalWeights σ * Q.conjTranspose)) *
        B * Q * diagonalWeights σ := by
      dsimp [rotatedGenerator]
      noncomm_ring
    _ = rotatedGenerator Q σ (A * B) := by
      rw [hi]
      dsimp [rotatedGenerator]
      noncomm_ring

lemma rotatedGenerator_product {d : ℕ} {Q : Square d} (hQ : IsUnitary Q)
    (σ : Fin d → ℝ) (hσ : ∀ i, σ i ≠ 0) (z : List (Square d)) :
    matrixProduct (z.map (rotatedGenerator Q σ)) = rotatedGenerator Q σ (matrixProduct z) := by
  induction z with
  | nil => simp [rotatedGenerator_one hQ σ hσ]
  | cons A z ih =>
      simp only [List.map_cons, matrixProduct_cons, ih, rotatedGenerator_mul hQ σ hσ]

lemma diagonalWeights_spectralNorm_le {d : ℕ} (σ : Fin d → ℝ) (b : ℝ)
    (hb : 0 ≤ b) (hσ : ∀ i, |σ i| ≤ b) : spectralNorm (diagonalWeights σ) ≤ b := by
  rw [spectralNorm, Matrix.l2_opNorm_toEuclideanCLM, diagonalWeights, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro i
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hσ i

lemma inverseDiagonalWeights_spectralNorm_le_one {d : ℕ} (τ : Fin d → ℝ)
    (hτ : ∀ i, 1 ≤ τ i) : spectralNorm (inverseDiagonalWeights τ) ≤ 1 := by
  change spectralNorm (diagonalWeights (fun i => (τ i)⁻¹)) ≤ 1
  apply diagonalWeights_spectralNorm_le _ _ zero_le_one
  intro i
  have hp : 0 < τ i := lt_of_lt_of_le zero_lt_one (hτ i)
  rw [abs_of_pos (inv_pos.mpr hp)]
  exact (inv_le_one₀ hp).mpr (hτ i)

lemma spectralNorm_unrotate_le {d : ℕ} {Q : Square d} (hQ : IsUnitary Q)
    (τ : Fin d → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hτ : ∀ i, 1 ≤ τ i ∧ τ i ≤ T) (A : Square d) :
    spectralNorm A ≤ T * spectralNorm (rotatedGenerator Q τ A) := by
  have hp : ∀ i, 0 < τ i := fun i => lt_of_lt_of_le zero_lt_one (hτ i).1
  have hD : spectralNorm (diagonalWeights τ) ≤ T :=
    diagonalWeights_spectralNorm_le τ T hT (fun i => by rw [abs_of_pos (hp i)]; exact (hτ i).2)
  have hU := inverseDiagonalWeights_spectralNorm_le_one τ (fun i => (hτ i).1)
  have hi := diagonal_inverse τ (fun i => (hp i).ne')
  have he : Q.conjTranspose * A * Q =
      diagonalWeights τ * rotatedGenerator Q τ A * inverseDiagonalWeights τ := by
    symm
    calc
      _ = (diagonalWeights τ * inverseDiagonalWeights τ) *
          (Q.conjTranspose * A * Q) * (diagonalWeights τ * inverseDiagonalWeights τ) := by
        dsimp [rotatedGenerator]
        noncomm_ring
      _ = Q.conjTranspose * A * Q := by rw [hi.1, one_mul, mul_one]
  calc
    spectralNorm A = spectralNorm (Q.conjTranspose * A * Q) := by
      rw [spectralNorm_unitary_right hQ, spectralNorm_unitary_left (isUnitary_star hQ)]
    _ = spectralNorm (diagonalWeights τ * rotatedGenerator Q τ A * inverseDiagonalWeights τ) :=
      congrArg spectralNorm he
    _ ≤ (spectralNorm (diagonalWeights τ) * spectralNorm (rotatedGenerator Q τ A)) *
        spectralNorm (inverseDiagonalWeights τ) :=
      (spectralNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (spectralNorm_mul_le _ _) (spectralNorm_nonneg _))
    _ ≤ (T * spectralNorm (rotatedGenerator Q τ A)) * 1 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hD (spectralNorm_nonneg _)) hU
        (spectralNorm_nonneg _) (mul_nonneg hT (spectralNorm_nonneg _))
    _ = T * spectralNorm (rotatedGenerator Q τ A) := mul_one _

#print axioms rotatedGenerator_product
#assert_trust kernel rotatedGenerator_product
#print axioms spectralNorm_unrotate_le
#assert_trust kernel spectralNorm_unrotate_le

end NLA.MF07
