/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Gram inverse, all four Penrose identities, and the actual Euclidean projected
norm. The generic lemmas work for arbitrary finite row/column index types.
-/
import NLA.IE17.Geometry
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Star.Real

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical Matrix.Norms.L2Operator
noncomputable section
namespace NLA.IE17

theorem dot_mulVec_left {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (x : κ → ℝ) (y : ι → ℝ) :
    dotProduct (M.mulVec x) y = dotProduct x (M.transpose.mulVec y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.transpose_apply]
  ring

theorem gram_pseudoinverse_penrose {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (K : Matrix ι κ ℝ)
    (hdet : IsUnit (K.transpose * K).det) :
    Penrose K ((K.transpose * K)⁻¹ * K.transpose) := by
  have hJK : ((K.transpose * K)⁻¹ * K.transpose) * K = 1 := by
    rw [Matrix.mul_assoc]
    exact Matrix.nonsing_inv_mul _ hdet
  have hG : (K.transpose * K).transpose = K.transpose * K := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, hJK, Matrix.mul_one]
  · rw [hJK, Matrix.one_mul]
  · simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_nonsing_inv, hG, Matrix.mul_assoc]
  · rw [hJK, Matrix.transpose_one]

theorem gram_projection_norm_sq {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (K : Matrix ι κ ℝ) (v : ι → ℝ)
    (hdet : IsUnit (K.transpose * K).det) :
    ‖(WithLp.toLp 2 ((K * ((K.transpose * K)⁻¹ * K.transpose)).mulVec v) :
        EuclideanSpace ℝ ι)‖ ^ 2 =
      dotProduct (K.transpose.mulVec v)
        ((K.transpose * K)⁻¹.mulVec (K.transpose.mulVec v)) := by
  let g := K.transpose.mulVec v
  let w := (K.transpose * K)⁻¹.mulVec g
  have hproj : (K * ((K.transpose * K)⁻¹ * K.transpose)).mulVec v = K.mulVec w := by
    simp only [w, g, ← Matrix.mulVec_mulVec]
  have hsolve : (K.transpose * K).mulVec w = g := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  calc
    _ = dotProduct (K.mulVec w) (K.mulVec w) := by
      rw [hproj, EuclideanSpace.real_norm_sq_eq]
      simp only [dotProduct, pow_two]
    _ = dotProduct w ((K.transpose * K).mulVec w) := by
      rw [dot_mulVec_left, Matrix.mulVec_mulVec]
    _ = dotProduct g w := by rw [hsolve, dotProduct_comm]

theorem augmented_gram {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    (augmentedMatrix A b x).transpose * augmentedMatrix A b x =
      A.transpose * A +
        (euclideanNorm (residual A b x) / euclideanNorm x) ^ 2 • (1 : Mat n n) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [augmentedMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
      pow_two]
  · simp [augmentedMatrix, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
      hij, Ne.symm hij]

theorem augmented_gram_posDef {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n)
    (hx : x ≠ 0) (hr : residual A b x ≠ 0) :
    ((augmentedMatrix A b x).transpose * augmentedMatrix A b x).PosDef := by
  rw [augmented_gram]
  have hA : (A.transpose * A).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self A
  have hscalar : 0 < (euclideanNorm (residual A b x) / euclideanNorm x) ^ 2 :=
    sq_pos_of_pos (div_pos (euclideanNorm_pos hr) (euclideanNorm_pos hx))
  exact Matrix.PosDef.posSemidef_add hA ((Matrix.PosDef.one : (1 : Mat n n).PosDef).smul hscalar)

theorem augmentedPseudoinverse_spec {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n)
    (hx : x ≠ 0) (hr : residual A b x ≠ 0) :
    IsUnit ((augmentedMatrix A b x).transpose * augmentedMatrix A b x).det ∧
    Penrose (augmentedMatrix A b x) (augmentedPseudoinverse A b x) := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp
    (augmented_gram_posDef A b x hx hr).isUnit
  exact ⟨hdet, gram_pseudoinverse_penrose _ hdet⟩

theorem augmented_transpose_residual {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    (augmentedMatrix A b x).transpose.mulVec
      (Sum.elim (residual A b x) (fun _ : Fin n => 0)) = normalResidual A b x := by
  ext i
  simp [augmentedMatrix, normalResidual, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

#assert_trust kernel gram_pseudoinverse_penrose
#assert_trust kernel augmentedPseudoinverse_spec

end NLA.IE17
