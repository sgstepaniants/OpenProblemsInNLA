/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Reconstruct the affine Hermitian matrix from the full normal diagonalization
and collinear eigenvalues, including the scalar and repeated-value cases.
-/
import NLA.MI04.Normality
import NLA.MI04.Diagonalization
import NLA.MI04.Geometry

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04

theorem pair_symmetry_essentially_hermitian {n : ℕ} (hn : 1 ≤ n) (X : Square n)
    (hX : PairMagnitudeSymmetry X) : EssentiallyHermitian X := by
  obtain ⟨U, z, hdiagonal⟩ := normal_unitary_diagonalization hn X
    (pair_symmetry_normal hn X hX)
  have hU : (U : Square n).conjTranspose * (U : Square n) = 1 :=
    Unitary.coe_star_mul_self U
  have hU' : (U : Square n) * (U : Square n).conjTranspose = 1 :=
    Unitary.coe_mul_star_self U
  have hsimilar : unitarySimilarity X U = Matrix.diagonal z := by
    change (U : Square n).conjTranspose * X * (U : Square n) = _
    rw [hdiagonal]
    calc
      (U : Square n).conjTranspose *
          ((U : Square n) * Matrix.diagonal z * (U : Square n).conjTranspose) *
          (U : Square n) =
          ((U : Square n).conjTranspose * (U : Square n)) * Matrix.diagonal z *
          ((U : Square n).conjTranspose * (U : Square n)) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal z := by rw [hU, one_mul, mul_one]
  have hpair : PairMagnitudeSymmetry (Matrix.diagonal z) := by
    rw [← hsimilar]
    exact pair_symmetry_unitary hn X hX U
  obtain ⟨α, β, t, ht⟩ := collinear_values_affine hn z
    (diagonal_pair_collinearity hn z hpair)
  have hdiag : Matrix.diagonal z = α • realDiagonal t + β • (1 : Square n) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [realDiagonal, ht]
    · simp [realDiagonal, Matrix.diagonal_apply, Matrix.one_apply, hij]
  let K : Square n := (U : Square n) * realDiagonal t * (U : Square n).conjTranspose
  refine ⟨K, Matrix.isHermitian_mul_mul_conjTranspose (U : Square n)
    (realDiagonal_isHermitian t), α, β, ?_⟩
  change X = α • ((U : Square n) * realDiagonal t * (U : Square n).conjTranspose) +
    β • (1 : Square n)
  rw [hdiagonal, hdiag]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_one, hU']

/-- Full original implication, retaining the universal positive-block premise. -/
theorem universal_positive_block_essentially_hermitian {n : ℕ} (hn : 1 ≤ n)
    (X : Square n)
    (hX : ∀ A B : Square n, A.IsHermitian → B.IsHermitian →
      (Matrix.fromBlocks A X X.conjTranspose B).PosSemidef →
        spectralNorm (Matrix.fromBlocks A X X.conjTranspose B) ≤ spectralNorm (A + B)) :
    ∃ K : Square n, K.IsHermitian ∧ ∃ α β : ℂ,
      X = α • K + β • (1 : Square n) := by
  exact pair_symmetry_essentially_hermitian hn X
    (orthonormal_pair_symmetry hn X (universal_to_extreme_symmetry hn X hX))

#print axioms pair_symmetry_essentially_hermitian
#assert_trust kernel pair_symmetry_essentially_hermitian
#print axioms universal_positive_block_essentially_hermitian
#assert_trust kernel universal_positive_block_essentially_hermitian

end NLA.MI04
