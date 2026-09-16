/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Use Mathlib's orthonormal-basis extension and actual change-of-basis unitary.
No dimension-two exception or coordinate-basis restriction is assumed.
-/
import NLA.MI04.Probes

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04

lemma orthonormal_set_basis {n : ℕ} (s : Set (CVector (Fin n)))
    (hs : Orthonormal ℂ (Subtype.val : s → CVector (Fin n))) :
    ∃ B : OrthonormalBasis (Fin n) ℂ (CVector (Fin n)), s ⊆ Set.range B := by
  obtain ⟨w, b, hsub, hb⟩ := hs.exists_orthonormalBasis_extension
  let e : ↥w ≃ Fin n := Fintype.equivFinOfCardEq
    ((Module.finrank_eq_card_basis b.toBasis).symm.trans finrank_euclideanSpace_fin)
  refine ⟨b.reindex e, ?_⟩
  intro u hu
  let iu : ↥w := ⟨u, hsub hu⟩
  refine ⟨e iu, ?_⟩
  rw [OrthonormalBasis.reindex_apply, e.symm_apply_apply]
  exact congrFun hb iu

lemma orthonormal_pair_set {n : ℕ} (u v : CVector (Fin n))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : inner ℂ u v = 0) :
    Orthonormal ℂ (Subtype.val : ({u, v} : Set (CVector (Fin n))) → CVector (Fin n)) := by
  classical
  have huu : inner ℂ u u = 1 := by simp [inner_self_eq_norm_sq, hu]
  have hvv : inner ℂ v v = 1 := by simp [inner_self_eq_norm_sq, hv]
  have hvu : inner ℂ v u = 0 := inner_eq_zero_symm.mp huv
  have hne : u ≠ v := by
    intro h
    have hz : (1 : ℂ) = 0 := by simpa only [← h, huu] using huv
    exact one_ne_zero hz
  rw [orthonormal_subtype_iff_ite]
  intro x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
    simp [hu, hv, huu, hvv, huv, hvu, hne, Ne.symm hne]

def basisUnitary {n : ℕ} (B : OrthonormalBasis (Fin n) ℂ (CVector (Fin n))) :
    Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix B,
    (EuclideanSpace.basisFun (Fin n) ℂ).toMatrix_orthonormalBasis_mem_unitary B⟩

lemma basisUnitary_entry {n : ℕ} (B : OrthonormalBasis (Fin n) ℂ (CVector (Fin n)))
    (i j : Fin n) : (basisUnitary B : Square n) i j = B j i := by
  simp [basisUnitary, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr]

lemma basisUnitary_action {n : ℕ} (B : OrthonormalBasis (Fin n) ℂ (CVector (Fin n)))
    (j : Fin n) : unitaryAction (basisUnitary B) (coordinateUnit j) = B j := by
  ext i
  rw [unitaryAction_apply, euclidean_matrix_apply]
  simp [coordinateUnit_apply, basisUnitary_entry]

lemma matrixCoefficient_coordinateUnits {n : ℕ} (X : Square n) (i j : Fin n) :
    matrixCoefficient X (coordinateUnit i) (coordinateUnit j) = X i j := by
  rw [matrixCoefficient, inner_coordinateUnit_left, euclidean_matrix_apply]
  simp [coordinateUnit_apply]

lemma matrixCoefficient_unitarySimilarity {n : ℕ} (X : Square n)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (u v : CVector (Fin n)) :
    matrixCoefficient (unitarySimilarity X U) u v =
      matrixCoefficient X (unitaryAction U u) (unitaryAction U v) :=
  inner_unitarySimilarity X U u v

lemma unitarySimilarity_entry_basis {n : ℕ} (X : Square n)
    (B : OrthonormalBasis (Fin n) ℂ (CVector (Fin n))) (i j : Fin n) :
    unitarySimilarity X (basisUnitary B) i j = matrixCoefficient X (B i) (B j) := by
  rw [← matrixCoefficient_coordinateUnits (unitarySimilarity X (basisUnitary B)) i j,
    matrixCoefficient_unitarySimilarity, basisUnitary_action, basisUnitary_action]

theorem orthonormal_pair_symmetry {n : ℕ} (hn : 1 ≤ n) (X : Square n)
    (hX : ExtremeSymmetry X) : PairMagnitudeSymmetry X := by
  intro u v hu hv huv
  obtain ⟨B, hB⟩ := orthonormal_set_basis ({u, v} : Set (CVector (Fin n)))
    (orthonormal_pair_set u v hu hv huv)
  obtain ⟨i, hi⟩ := hB (by simp : u ∈ ({u, v} : Set (CVector (Fin n))))
  obtain ⟨j, hj⟩ := hB (by simp : v ∈ ({u, v} : Set (CVector (Fin n))))
  have hs := offDiagonal_magnitude_symmetry hn (unitarySimilarity X (basisUnitary B))
    (extreme_symmetry_unitary hn X hX (basisUnitary B)) i j
  rw [unitarySimilarity_entry_basis, unitarySimilarity_entry_basis, hi, hj,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hs
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hs

#print axioms orthonormal_pair_symmetry
#assert_trust kernel orthonormal_pair_symmetry

end NLA.MI04
