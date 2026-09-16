/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original norm-rounding argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

This constructs the required singular coordinates from Mathlib's ordered
spectral basis of the positive Gram matrix. No singular decomposition is
postulated. Positive weights and their ordering are proved explicitly.
-/
import NLA.MF07.Auerbach
import NLA.MF07.UnitaryGeometry
import Mathlib.Analysis.Matrix.PosDef

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators ComplexOrder

noncomputable section
namespace NLA.MF07

lemma norm_applyMatrix_unitary {d : ℕ} (hd : 1 ≤ d) {Q : Square d}
    (hQ : IsUnitary Q) (x : EuclideanVector d) : ‖applyMatrix Q x‖ = ‖x‖ := by
  have hn : spectralNorm Q = 1 := by
    simpa only [mul_one, spectralNorm_one hd] using
      spectralNorm_unitary_left hQ (1 : Square d)
  have hns : spectralNorm Q.conjTranspose = 1 := by
    simpa only [mul_one, spectralNorm_one hd] using
      spectralNorm_unitary_left (isUnitary_star hQ) (1 : Square d)
  apply le_antisymm
  · simpa only [hn, one_mul] using norm_applyMatrix_le Q x
  · have hh := norm_applyMatrix_le Q.conjTranspose (applyMatrix Q x)
    simpa only [← applyMatrix_mul, hQ.1, applyMatrix_one, hns, one_mul] using hh

lemma diagonalWeights_star {d : ℕ} (σ : Fin d → ℝ) :
    (diagonalWeights σ).conjTranspose = diagonalWeights σ := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [diagonalWeights, Matrix.conjTranspose_apply]
  · simp [diagonalWeights, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hij, Ne.symm hij]

lemma inverseDiagonalWeights_star {d : ℕ} (σ : Fin d → ℝ) :
    (inverseDiagonalWeights σ).conjTranspose = inverseDiagonalWeights σ := by
  exact diagonalWeights_star (fun i => (σ i)⁻¹)

lemma ordered_positive_gram_coordinates {d : ℕ} (T : Square d) (hT : T.det ≠ 0) :
    ∃ (Q : Square d) (λ : Fin d → ℝ), IsUnitary Q ∧ (∀ i, 0 < λ i) ∧
      Antitone λ ∧ (T * T.conjTranspose) * Q = Q * diagonalWeights λ := by
  classical
  let H := T * T.conjTranspose
  have hH : H.IsHermitian := Matrix.isHermitian_mul_conjTranspose_self T
  have hS : H.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hH
  have hdim : Module.finrank ℂ (EuclideanVector d) = d := finrank_euclideanSpace_fin
  let b := hS.eigenvectorBasis hdim
  let λ := hS.eigenvalues hdim
  let Q := columnMatrix b
  have hQmem : Q ∈ Matrix.unitaryGroup (Fin d) ℂ := by
    change (EuclideanSpace.basisFun (Fin d) ℂ).toBasis.toMatrix b.toBasis ∈ _
    exact (EuclideanSpace.basisFun (Fin d) ℂ).toMatrix_orthonormalBasis_mem_unitary b
  have hQ : IsUnitary Q := by
    simpa only [IsUnitary, Unitary.mem_iff, Matrix.star_eq_conjTranspose] using hQmem
  have hHQ : H * Q = Q * diagonalWeights λ := by
    ext i j
    have he : applyMatrix H (b j) = (λ j : ℂ) • b j :=
      hS.apply_eigenvectorBasis hdim j
    have hi := congrArg (fun x : EuclideanVector d => x i) he
    simpa [applyMatrix_coordinate, Q, columnMatrix, diagonalWeights, Matrix.mul_apply,
      Matrix.mul_diagonal, PiLp.smul_apply, mul_comm] using hi
  have hconj : Q.conjTranspose * H * Q = diagonalWeights λ := by
    calc
      Q.conjTranspose * H * Q = Q.conjTranspose * (H * Q) := mul_assoc _ _ _
      _ = Q.conjTranspose * (Q * diagonalWeights λ) := by rw [hHQ]
      _ = (Q.conjTranspose * Q) * diagonalWeights λ := (mul_assoc _ _ _).symm
      _ = diagonalWeights λ := by rw [hQ.1, one_mul]
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr (isUnit_iff_ne_zero.mpr hT)
  have hHp : H.PosDef := Matrix.PosDef.mul_conjTranspose_self T
    (Matrix.vecMul_injective_iff_isUnit.mpr hTu)
  have hQu : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).mpr
    (isUnit_iff_ne_zero.mpr (Matrix.det_ne_zero_of_left_inverse hQ.1))
  have hdiag : (diagonalWeights λ).PosDef := by
    rw [← hconj]
    exact hHp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hQu)
  have hλ : ∀ i, 0 < λ i := by
    intro i
    have hi := (Matrix.posDef_diagonal_iff.mp hdiag) i
    simpa using hi
  exact ⟨Q, λ, hQ, hλ, hS.eigenvalues_antitone hdim, hHQ⟩

/-- A full singular-coordinate factorization, with decreasing positive weights. -/
lemma exists_singular_coordinates {d : ℕ} (T : Square d) (hT : T.det ≠ 0) :
    ∃ (Q R : Square d) (σ : Fin d → ℝ),
      IsUnitary Q ∧ IsUnitary R ∧ (∀ i, 0 < σ i) ∧ Antitone σ ∧
      T * R = Q * diagonalWeights σ := by
  obtain ⟨Q, λ, hQ, hλ, hmono, hHQ⟩ := ordered_positive_gram_coordinates T hT
  let σ : Fin d → ℝ := fun i => Real.sqrt (λ i)
  have hσ : ∀ i, 0 < σ i := fun i => Real.sqrt_pos.mpr (hλ i)
  have hσmono : Antitone σ := fun i j hij => Real.sqrt_le_sqrt (hmono hij)
  have hD : diagonalWeights σ * diagonalWeights σ = diagonalWeights λ := by
    ext i j
    by_cases hij : i = j
    · subst j
      have hi := congrArg Complex.ofReal (Real.mul_self_sqrt (hλ i).le)
      simpa [diagonalWeights, σ] using hi
    · simp [diagonalWeights, Matrix.diagonal_apply, hij]
  have hinv := diagonal_inverse σ (fun i => (hσ i).ne')
  let R := T.conjTranspose * Q * inverseDiagonalWeights σ
  have hTR : T * R = Q * diagonalWeights σ := by
    calc
      T * R = ((T * T.conjTranspose) * Q) * inverseDiagonalWeights σ := by
        dsimp [R]
        noncomm_ring
      _ = (Q * (diagonalWeights σ * diagonalWeights σ)) * inverseDiagonalWeights σ := by
        rw [hHQ, hD]
      _ = Q * diagonalWeights σ * (diagonalWeights σ * inverseDiagonalWeights σ) := by
        noncomm_ring
      _ = Q * diagonalWeights σ := by rw [hinv.1, mul_one]
  have hRleft : R.conjTranspose * R = 1 := by
    calc
      R.conjTranspose * R =
          inverseDiagonalWeights σ * Q.conjTranspose *
            ((T * T.conjTranspose) * Q) * inverseDiagonalWeights σ := by
        dsimp [R]
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          inverseDiagonalWeights_star, Matrix.conjTranspose_conjTranspose]
        noncomm_ring
      _ = inverseDiagonalWeights σ * (Q.conjTranspose * Q) *
          (diagonalWeights σ * diagonalWeights σ) * inverseDiagonalWeights σ := by
        rw [hHQ, ← hD]
        noncomm_ring
      _ = (inverseDiagonalWeights σ * diagonalWeights σ) *
          (diagonalWeights σ * inverseDiagonalWeights σ) := by
        rw [hQ.1]
        noncomm_ring
      _ = 1 := by rw [hinv.2, hinv.1, one_mul]
  have hR : IsUnitary R := ⟨hRleft, Matrix.mul_eq_one_comm.mp hRleft⟩
  exact ⟨Q, R, σ, hQ, hR, hσ, hσmono, hTR⟩

#print axioms ordered_positive_gram_coordinates
#assert_trust kernel ordered_positive_gram_coordinates
#print axioms exists_singular_coordinates
#assert_trust kernel exists_singular_coordinates

end NLA.MF07
