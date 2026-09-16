/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Extend each unit vector to an orthonormal basis, compare every Parseval term,
then use the genuine operator/adjoint norm criterion for normality.
-/
import NLA.MI04.BasisTransport

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04

lemma orthonormal_singleton_set {n : ℕ} (u : CVector (Fin n)) (hu : ‖u‖ = 1) :
    Orthonormal ℂ (Subtype.val : ({u} : Set (CVector (Fin n))) → CVector (Fin n)) := by
  classical
  rw [orthonormal_subtype_iff_ite]
  intro x hx y hy
  simp only [Set.mem_singleton_iff] at hx hy
  subst x
  subst y
  simp [inner_self_eq_norm_sq, hu]

lemma pair_symmetry_unit_norm_adjoint {n : ℕ} (X : Square n)
    (hX : PairMagnitudeSymmetry X) (u : CVector (Fin n)) (hu : ‖u‖ = 1) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X u‖ =
      ‖ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) u‖ := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X
  obtain ⟨B, hB⟩ := orthonormal_set_basis ({u} : Set (CVector (Fin n)))
    (orthonormal_singleton_set u hu)
  obtain ⟨i, hi⟩ := hB (by simp : u ∈ ({u} : Set (CVector (Fin n))))
  have hterm (j : Fin n) :
      ‖inner ℂ (B j) (T u)‖ = ‖inner ℂ (B j) (ContinuousLinearMap.adjoint T u)‖ := by
    rw [ContinuousLinearMap.adjoint_inner_right, norm_inner_symm (T (B j)) u]
    change ‖matrixCoefficient X (B j) u‖ = ‖matrixCoefficient X u (B j)‖
    by_cases hj : j = i
    · subst j
      rw [hi]
    · apply hX (B j) u (B.orthonormal.norm_eq_one j) hu
      rw [← hi]
      exact B.orthonormal.inner_eq_zero hj
  have hsquare : ‖T u‖ ^ 2 = ‖ContinuousLinearMap.adjoint T u‖ ^ 2 := by
    rw [← B.sum_sq_norm_inner_right (T u),
      ← B.sum_sq_norm_inner_right (ContinuousLinearMap.adjoint T u)]
    exact Finset.sum_congr rfl (fun j _ => congrArg (fun x : ℝ => x ^ 2) (hterm j))
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare

lemma pair_symmetry_norm_adjoint {n : ℕ} (X : Square n)
    (hX : PairMagnitudeSymmetry X) (v : CVector (Fin n)) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X v‖ =
      ‖ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hnv : ‖v‖ ≠ 0 := (norm_pos_iff.mpr hv).ne'
  let c : ℂ := ((‖v‖⁻¹ : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast inv_ne_zero hnv
  have hcnorm : ‖c‖ = ‖v‖⁻¹ := by
    simp [c, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
  have hu : ‖c • v‖ = 1 := by
    rw [norm_smul, hcnorm, inv_mul_cancel₀ hnv]
  have h := pair_symmetry_unit_norm_adjoint X hX (c • v) hu
  simp only [map_smul, norm_smul] at h
  exact mul_left_cancel₀ (norm_pos_iff.mpr hc).ne' h

theorem pair_symmetry_normal {n : ℕ} (hn : 1 ≤ n) (X : Square n)
    (hX : PairMagnitudeSymmetry X) : X.conjTranspose * X = X * X.conjTranspose := by
  have hnormal : IsStarNormal (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) :=
    ContinuousLinearMap.isStarNormal_iff_norm_eq_adjoint.mpr
      (pair_symmetry_norm_adjoint X hX)
  have he : star (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) *
        Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X =
      Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X *
        star (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X) :=
    hnormal.star_comm_self
  apply (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).injective
  simpa only [← Matrix.star_eq_conjTranspose, map_mul, map_star] using he

#print axioms pair_symmetry_normal
#assert_trust kernel pair_symmetry_normal

end NLA.MI04
