/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original norm-rounding argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The factor d follows from two finite Cauchy--Schwarz bounds around the actual
maximal-determinant basis. The coordinate map is the singular decomposition
constructed in SingularCoordinates, with every diagonal weight positive.
-/
import NLA.MF07.SingularCoordinates
import NLA.MF07.ApproximateNorm

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF07

lemma complexNorm_transport {d : ℕ} {v : EuclideanVector d → ℝ} (hv : IsComplexNorm v)
    (P U : Square d) (hUP : U * P = 1) (r : ℝ) (hr : 0 < r) :
    IsComplexNorm (fun x => r * v (applyMatrix P x)) := by
  refine ⟨fun x => mul_nonneg hr.le (hv.1 _), ?_, ?_, ?_⟩
  · intro x
    constructor
    · intro hx
      have hv0 : v (applyMatrix P x) = 0 := (mul_eq_zero.mp hx).resolve_left hr.ne'
      have hp0 := (hv.2.1 _).mp hv0
      have he := congrArg (applyMatrix U) hp0
      simpa only [← applyMatrix_mul, hUP, applyMatrix_one, applyMatrix_zero] using he
    · intro hx
      simp [hx, complexNorm_zero hv]
  · intro x y
    simpa only [applyMatrix_add_vector, mul_add] using
      mul_le_mul_of_nonneg_left (hv.2.2.1 (applyMatrix P x) (applyMatrix P y)) hr.le
  · intro c x
    rw [applyMatrix_smul_vector, hv.2.2.2]
    ring

lemma rotatedGenerator_entry_bound {d : ℕ} (hd : 1 ≤ d) {Q : Square d}
    (hQ : IsUnitary Q) (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    (A : Square d) (L : ℝ) (hA : spectralNorm A ≤ L) (i j : Fin d) :
    ‖rotatedGenerator Q σ A i j‖ ≤ L * σ j / σ i := by
  have hm : rotatedGenerator Q σ A =
      inverseDiagonalWeights σ * (Q.conjTranspose * A * Q) * diagonalWeights σ := by
    dsimp [rotatedGenerator]
    noncomm_ring
  have he : rotatedGenerator Q σ A i j =
      ((σ i)⁻¹ : ℂ) * (Q.conjTranspose * A * Q) i j * (σ j : ℂ) := by
    rw [hm]
    simp [diagonalWeights, inverseDiagonalWeights, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hb : ‖(Q.conjTranspose * A * Q) i j‖ ≤ L := by
    apply (spectralNorm_entry_bound _ i j).trans
    rw [spectralNorm_unitary_right hQ, spectralNorm_unitary_left (isUnitary_star hQ)]
    exact hA
  rw [he, norm_mul, norm_mul]
  have hn1 : ‖((σ i)⁻¹ : ℂ)‖ = (σ i)⁻¹ := by
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hσ i)]
  have hn2 : ‖(σ j : ℂ)‖ = σ j := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hσ j)]
  rw [hn1, hn2]
  calc
    (σ i)⁻¹ * ‖(Q.conjTranspose * A * Q) i j‖ * σ j ≤ (σ i)⁻¹ * L * σ j :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (hσ i).le))
        (hσ j).le
    _ = L * σ j / σ i := by ring

theorem rounded_extremal_norm {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (hr : jointSpectralRadius M = 1)
    (a : ℝ) (ha : 1 < a) :
    ∃ (Q : Square d) (σ : Fin d → ℝ) (w : EuclideanVector d → ℝ),
      IsUnitary Q ∧ Antitone σ ∧ (∀ i, 0 < σ i) ∧ IsComplexNorm w ∧
      (∀ x, ‖x‖ ≤ w x ∧ w x ≤ (d : ℝ) * ‖x‖) ∧
      (∀ A ∈ M, ∀ x, w (applyMatrix (rotatedGenerator Q σ A) x) ≤ a * w x) ∧
      ∀ A ∈ M, ∀ i j : Fin d,
        ‖rotatedGenerator Q σ A i j‖ ≤ familyNorm M * σ j / σ i := by
  obtain ⟨v, c, hc, hv, hbound, hgen⟩ := approximate_extremal_norm hd M hM hne hr a ha
  obtain ⟨T, hT, hcoords⟩ := exists_auerbach_coordinates hv c hc hbound
  obtain ⟨Q, R, σ, hQ, hR, hσ, hmono, hTR⟩ := exists_singular_coordinates T hT
  let P := Q * diagonalWeights σ
  let U := inverseDiagonalWeights σ * Q.conjTranspose
  let r := Real.sqrt (d : ℝ)
  let w : EuclideanVector d → ℝ := fun x => r * v (applyMatrix P x)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hrpos : 0 < r := Real.sqrt_pos.mpr hdpos
  have hrsq : r * r = (d : ℝ) := Real.mul_self_sqrt hdpos.le
  have hinv := diagonal_inverse σ (fun i => (hσ i).ne')
  have hUP : U * P = 1 := by
    calc
      U * P = inverseDiagonalWeights σ * (Q.conjTranspose * Q) * diagonalWeights σ := by
        dsimp [U, P]
        noncomm_ring
      _ = 1 := by rw [hQ.1, mul_one, hinv.2]
  have hPU : P * U = 1 := by
    calc
      P * U = Q * (diagonalWeights σ * inverseDiagonalWeights σ) * Q.conjTranspose := by
        dsimp [P, U]
        noncomm_ring
      _ = 1 := by rw [hinv.1, mul_one, hQ.2]
  have hw : IsComplexNorm w := complexNorm_transport hv P U hUP r hrpos
  have hwb : ∀ x, ‖x‖ ≤ w x ∧ w x ≤ (d : ℝ) * ‖x‖ := by
    intro x
    have hb := hcoords (applyMatrix R x)
    have he : applyMatrix P x = applyMatrix T (applyMatrix R x) := by
      rw [← applyMatrix_mul, hTR]
    have hn := norm_applyMatrix_unitary hd hR x
    refine ⟨?_, ?_⟩
    · simpa only [w, r, he, hn] using hb.1
    · calc
        w x = r * v (applyMatrix T (applyMatrix R x)) := by rw [w, he]
        _ ≤ r * (r * ‖x‖) := by
          apply mul_le_mul_of_nonneg_left _ hrpos.le
          simpa only [r, hn] using hb.2
        _ = (d : ℝ) * ‖x‖ := by rw [← mul_assoc, hrsq]
  have hconj : ∀ A, P * rotatedGenerator Q σ A = A * P := by
    intro A
    have he : rotatedGenerator Q σ A = U * A * P := by
      dsimp [rotatedGenerator, U, P]
      noncomm_ring
    rw [he]
    calc
      P * (U * A * P) = (P * U) * (A * P) := by noncomm_ring
      _ = A * P := by rw [hPU, one_mul]
  refine ⟨Q, σ, w, hQ, hmono, hσ, hw, hwb, ?_, ?_⟩
  · intro A hA x
    calc
      w (applyMatrix (rotatedGenerator Q σ A) x) =
          r * v (applyMatrix A (applyMatrix P x)) := by
        rw [w, ← applyMatrix_mul, hconj, applyMatrix_mul]
      _ ≤ r * (a * v (applyMatrix P x)) :=
        mul_le_mul_of_nonneg_left (hgen A hA _) hrpos.le
      _ = a * w x := by dsimp [w]; ring
  · intro A hA i j
    exact rotatedGenerator_entry_bound hd hQ σ hσ A (familyNorm M)
      ((family_norm_maximum hd M hM hne).2.2 A hA) i j

#print axioms rounded_extremal_norm
#assert_trust kernel rounded_extremal_norm

end NLA.MF07
