/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Exact coordinate identities for the dimension-independent Rayleigh sandwich.
-/
import NLA.MI04.Quadratic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder

namespace NLA.MI04
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateUnit (a : ι) : CVector ι := EuclideanSpace.single a 1

@[simp] lemma coordinateUnit_apply (a j : ι) :
    coordinateUnit a j = if j = a then 1 else 0 := by
  simp [coordinateUnit, PiLp.single_apply]

@[simp] lemma coordinateUnit_norm (a : ι) : ‖coordinateUnit a‖ = 1 := by
  simp [coordinateUnit]

lemma inner_coordinateUnit_left (a : ι) (v : CVector ι) :
    inner ℂ (coordinateUnit a) v = v a := by
  simp [coordinateUnit, EuclideanSpace.inner_single_left]

lemma inner_coordinateUnit_right (a : ι) (v : CVector ι) :
    inner ℂ v (coordinateUnit a) = star (v a) := by
  simp [coordinateUnit, EuclideanSpace.inner_single_right, Complex.star_def]

lemma euclidean_matrix_apply (M : CMatrix ι) (v : CVector ι) (i : ι) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M v i = ∑ j, M i j * v j := by
  rfl

lemma norm_sq_eq_sum_normSq (v : CVector ι) :
    ‖v‖ ^ 2 = ∑ j, Complex.normSq (v j) := by
  simp only [EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]

lemma realQuadratic_coordinateUnit (M : CMatrix ι) (a : ι) :
    realQuadratic M (coordinateUnit a) = (M a a).re := by
  rw [realQuadratic, inner_coordinateUnit_left, euclidean_matrix_apply]
  simp [coordinateUnit_apply]

lemma realQuadratic_diagonal (d : ι → ℝ) (v : CVector ι) :
    realQuadratic (realDiagonal d) v = ∑ j, d j * Complex.normSq (v j) := by
  simp only [realQuadratic, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.ofLp_toEuclideanCLM, realDiagonal, dotProduct, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.mulVec_diagonal]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.star_def] <;> ring

lemma realQuadratic_add_vectors (M : CMatrix ι) (hM : M.IsHermitian)
    (v w : CVector ι) :
    realQuadratic M (v + w) = realQuadratic M v + realQuadratic M w +
      2 * (inner ℂ v (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M w)).re := by
  have hs : inner ℂ (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M v) w =
      inner ℂ v (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M w) :=
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hM) v w
  have hr := inner_re_symm (𝕜 := ℂ) w
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M v)
  have hs' := congrArg Complex.re hs
  simp only [realQuadratic, map_add, inner_add_left, inner_add_right, Complex.add_re]
  linarith

lemma realQuadratic_real_perturbed_vector (M : CMatrix ι) (hM : M.IsHermitian)
    (v w : CVector ι) (ε : ℝ) :
    realQuadratic M (v + (ε : ℂ) • w) = realQuadratic M v +
      ε ^ 2 * realQuadratic M w +
      2 * ε * (inner ℂ v (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M w)).re := by
  rw [realQuadratic_add_vectors M hM, realQuadratic_smul_vector]
  simp [map_smul, inner_smul_right, Complex.mul_re,
    Complex.norm_real, Real.norm_eq_abs, sq_abs] <;> ring

lemma coordinateUnit_add_norm_sq (a : ι) (w : CVector ι) (hw : w a = 0) (ε : ℝ) :
    ‖coordinateUnit a + (ε : ℂ) • w‖ ^ 2 = 1 + ε ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq (𝕜 := ℂ), coordinateUnit_norm]
  simp [inner_smul_right, inner_coordinateUnit_left, hw,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

lemma realDiagonal_isHermitian (d : ι → ℝ) : (realDiagonal d).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases h : i = j
  · subst j
    simp [realDiagonal]
  · simp [realDiagonal, Matrix.diagonal_apply, h, h.symm]

lemma perturbedDiagonal_isHermitian (d : ι → ℝ) (V : CMatrix ι)
    (hV : V.IsHermitian) (ε : ℝ) : (perturbedDiagonal d V ε).IsHermitian :=
  (realDiagonal_isHermitian d).add (hermitian_real_smul V hV ε)

#print axioms realQuadratic_diagonal
#assert_trust kernel realQuadratic_diagonal
#print axioms realQuadratic_real_perturbed_vector
#assert_trust kernel realQuadratic_real_perturbed_vector

end NLA.MI04
