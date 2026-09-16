/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

The literal matrix unitary action on complex Euclidean space.
-/
import NLA.MI04.Rayleigh

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04
section FiniteCoordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def unitaryAction (U : Matrix.unitaryGroup ι ℂ) : CVector ι ≃ₗᵢ[ℂ] CVector ι :=
  Unitary.linearIsometryEquiv
    ⟨Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (U : CMatrix ι),
      Unitary.map_mem (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) U.property⟩

@[simp] lemma unitaryAction_apply (U : Matrix.unitaryGroup ι ℂ) (v : CVector ι) :
    unitaryAction U v = Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (U : CMatrix ι) v :=
  rfl

lemma inner_unitarySimilarity (M : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ)
    (u v : CVector ι) :
    inner ℂ u (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (unitarySimilarity M U) v) =
      inner ℂ (unitaryAction U u)
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M (unitaryAction U v)) := by
  change inner ℂ u
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
        (star (U : CMatrix ι) * M * (U : CMatrix ι)) v) =
    inner ℂ (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (U : CMatrix ι) u)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M
        (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) (U : CMatrix ι) v))
  simp only [map_mul, map_star, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

lemma realQuadratic_unitarySimilarity (M : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ)
    (v : CVector ι) :
    realQuadratic (unitarySimilarity M U) v = realQuadratic M (unitaryAction U v) := by
  exact congrArg Complex.re (inner_unitarySimilarity M U v v)

lemma unitarySimilarity_isHermitian (M : CMatrix ι) (hM : M.IsHermitian)
    (U : Matrix.unitaryGroup ι ℂ) : (unitarySimilarity M U).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_mul (U : CMatrix ι) hM

variable [Nonempty ι]

lemma topValue_unitarySimilarity (M : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) :
    topValue (unitarySimilarity M U) = topValue M := by
  apply le_antisymm
  · apply (topValue_le_iff _ _).mpr
    intro v hv
    rw [realQuadratic_unitarySimilarity]
    apply realQuadratic_le_top_of_unit
    simpa only [(unitaryAction U).norm_map] using hv
  · obtain ⟨u, hu, he, _⟩ := topValue_attained M
    have hu' : ‖(unitaryAction U).symm u‖ = 1 := by
      simpa only [(unitaryAction U).symm.norm_map] using hu
    have h := realQuadratic_le_top_of_unit (unitarySimilarity M U)
      ((unitaryAction U).symm u) hu'
    rw [realQuadratic_unitarySimilarity, (unitaryAction U).apply_symm_apply, he] at h
    exact h

theorem unitary_topValue (M : CMatrix ι) (_hM : M.IsHermitian)
    (U : Matrix.unitaryGroup ι ℂ) :
    topValue (unitarySimilarity M U) = topValue M :=
  topValue_unitarySimilarity M U

end FiniteCoordinates

theorem pair_symmetry_unitary {n : ℕ} (_hn : 1 ≤ n) (X : Square n)
    (hX : PairMagnitudeSymmetry X) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    PairMagnitudeSymmetry (unitarySimilarity X U) := by
  intro u v hu hv huv
  have hu' : ‖unitaryAction U u‖ = 1 := by
    simpa only [(unitaryAction U).norm_map] using hu
  have hv' : ‖unitaryAction U v‖ = 1 := by
    simpa only [(unitaryAction U).norm_map] using hv
  have huv' : inner ℂ (unitaryAction U u) (unitaryAction U v) = 0 := by
    rw [(unitaryAction U).inner_map_map]
    exact huv
  simpa only [matrixCoefficient, inner_unitarySimilarity] using
    hX (unitaryAction U u) (unitaryAction U v) hu' hv' huv'

#print axioms unitary_topValue
#assert_trust kernel unitary_topValue
#print axioms pair_symmetry_unitary
#assert_trust kernel pair_symmetry_unitary

end NLA.MI04
