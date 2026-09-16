/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Decompose an arbitrary vector into one coordinate and its orthogonal remainder.
-/
import NLA.MI04.Coordinates

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder

namespace NLA.MI04
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def puncturedVector (a : ι) (v : CVector ι) : CVector ι :=
  WithLp.toLp 2 (fun j => if j = a then 0 else v j)

@[simp] lemma puncturedVector_apply (a : ι) (v : CVector ι) (j : ι) :
    puncturedVector a v j = if j = a then 0 else v j := rfl

lemma punctured_decomposition (a : ι) (v : CVector ι) :
    v = puncturedVector a v + v a • coordinateUnit a := by
  ext j
  by_cases hj : j = a
  · subst j
    simp [PiLp.add_apply, PiLp.smul_apply]
  · simp [PiLp.add_apply, PiLp.smul_apply, hj]

lemma punctured_norm_sq (a : ι) (v : CVector ι) :
    ‖puncturedVector a v‖ ^ 2 = ∑ j, if j = a then 0 else Complex.normSq (v j) := by
  rw [norm_sq_eq_sum_normSq]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = a <;> simp [hj]

lemma coordinate_normSq_le (a : ι) (v : CVector ι) :
    Complex.normSq (v a) ≤ ‖v‖ ^ 2 := by
  rw [norm_sq_eq_sum_normSq]
  exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (v j)) (Finset.mem_univ a)

lemma euclidean_matrix_coordinateUnit (V : CMatrix ι) (a j : ι) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) V (coordinateUnit a) j = V j a := by
  rw [euclidean_matrix_apply]
  simp [coordinateUnit_apply]

lemma inner_matrix_coordinateUnit (V : CMatrix ι) (a : ι) (v : CVector ι) (c : ℂ) :
    inner ℂ v (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) V (c • coordinateUnit a)) =
      ∑ j, c * V j a * star (v j) := by
  rw [map_smul, inner_smul_right, EuclideanSpace.inner_eq_star_dotProduct]
  change c * (∑ j,
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) V (coordinateUnit a) j) * star (v j)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [euclidean_matrix_coordinateUnit]
  ring

lemma punctured_quadratic (V : CMatrix ι) (hV : V.IsHermitian)
    (a : ι) (haa : V a a = 0) (v : CVector ι) :
    realQuadratic V v = realQuadratic V (puncturedVector a v) +
      2 * ∑ j, if j = a then 0 else (v a * V j a * star (v j)).re := by
  have h := realQuadratic_add_vectors V hV (puncturedVector a v)
    (v a • coordinateUnit a)
  rw [← punctured_decomposition, realQuadratic_smul_vector,
    realQuadratic_coordinateUnit, haa, Complex.zero_re, mul_zero, add_zero,
    inner_matrix_coordinateUnit, Complex.re_sum] at h
  rw [h]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = a <;> simp [hj]

lemma diagonal_gap_identity (d : ι → ℝ) (a : ι) (ha : d a = 1) (v : CVector ι) :
    realQuadratic (realDiagonal d) v = ‖v‖ ^ 2 -
      ∑ j, if j = a then 0 else (1 - d j) * Complex.normSq (v j) := by
  rw [realQuadratic_diagonal, norm_sq_eq_sum_normSq, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = a
  · subst j
    simp [ha]
  · simp only [if_neg hj]
    ring

lemma perturbation_all_vector_bound (d : ι → ℝ) (V : CMatrix ι) (a : ι)
    (ha : d a = 1) (hV : V.IsHermitian) (haa : V a a = 0)
    (ε : ℝ) (hε : 0 ≤ ε) (v : CVector ι) :
    realQuadratic (perturbedDiagonal d V ε) v - ‖v‖ ^ 2 ≤
      ∑ j, if j = a then 0 else
        2 * ε * (v a * V j a * star (v j)).re -
          (1 - d j - ε * spectralNorm V) * Complex.normSq (v j) := by
  have hrest := realQuadratic_le_spectralNorm V (puncturedVector a v)
  rw [punctured_norm_sq] at hrest
  have he := mul_le_mul_of_nonneg_left hrest hε
  rw [perturbedDiagonal, realQuadratic_add, realQuadratic_smul_matrix,
    diagonal_gap_identity d a ha, punctured_quadratic V hV a haa]
  have hsum :
      (∑ j, if j = a then 0 else
        2 * ε * (v a * V j a * star (v j)).re -
          (1 - d j - ε * spectralNorm V) * Complex.normSq (v j)) =
      2 * ε * (∑ j, if j = a then 0 else (v a * V j a * star (v j)).re) -
        (∑ j, if j = a then 0 else (1 - d j) * Complex.normSq (v j)) +
        ε * spectralNorm V * (∑ j, if j = a then 0 else Complex.normSq (v j)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = a <;> simp only [hj, if_true, if_false] <;> ring
  rw [hsum]
  nlinarith only [he]

#print axioms perturbation_all_vector_bound
#assert_trust kernel perturbation_all_vector_bound

end NLA.MI04
