/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

The original augmented Moore-Penrose projection is reduced algebraically to
three rational divisions for this diagonal witness. This avoids square-root
intervals and numerical inversion while retaining the full original target.
-/
import NLA.IE17.ProjectionAlgebra
import NLA.IE17.ExactData
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical Matrix.Norms.L2Operator
noncomputable section
namespace NLA.IE17

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

theorem projectionError_sq_formula {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n)
    (hx : x ≠ 0) (hr : residual A b x ≠ 0) :
    projectionError A b x ^ 2 =
      realDot (normalResidual A b x)
        (Matrix.mulVec
          ((normSq x • (A.transpose * A) + normSq (residual A b x) • (1 : Mat n n))⁻¹)
          (normalResidual A b x)) := by
  by_cases hg : normalResidual A b x = 0
  · simp [projectionError, hg, realDot]
  let K := augmentedMatrix A b x
  let G := K.transpose * K
  let v : Fin m ⊕ Fin n → ℝ := Sum.elim (residual A b x) (fun _ => 0)
  have hdet : IsUnit G.det := (augmentedPseudoinverse_spec A b x hx hr).1
  have hs : normSq x ≠ 0 := (normSq_pos hx).ne'
  have hscale : normSq x • G =
      normSq x • (A.transpose * A) + normSq (residual A b x) • (1 : Mat n n) := by
    dsimp [G, K]
    rw [augmented_gram, smul_add, smul_smul]
    congr 1
    congr 1
    rw [div_pow, euclideanNorm_sq, euclideanNorm_sq]
    field_simp
  have hinv : (normSq x • G)⁻¹ = (normSq x)⁻¹ • G⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Matrix.nonsing_inv_mul G hdet, inv_mul_cancel₀ hs, one_smul]
  have hnorm :
      ‖(WithLp.toLp 2 ((K * (G⁻¹ * K.transpose)).mulVec v) :
        EuclideanSpace ℝ (Fin m ⊕ Fin n))‖ ^ 2 =
      realDot (normalResidual A b x) (G⁻¹.mulVec (normalResidual A b x)) := by
    simpa only [K, G, v, augmented_transpose_residual, realDot, dotProduct] using
      gram_projection_norm_sq K v hdet
  simp only [projectionError, hg, if_false, div_pow]
  change ‖(WithLp.toLp 2 ((K * (G⁻¹ * K.transpose)).mulVec v) :
      EuclideanSpace ℝ (Fin m ⊕ Fin n))‖ ^ 2 / euclideanNorm x ^ 2 = _
  rw [hnorm, euclideanNorm_sq, ← hscale, hinv]
  simp [realDot, Matrix.smul_mulVec, Finset.mul_sum, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc]

theorem inverse_diagonal_nonzero {n : ℕ} (d : Vec n) (hd : ∀ i, d i ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun i => (d i)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply, hd]
  · simp [Matrix.diagonal_apply, Matrix.one_apply, hij]

theorem witness_projection_formula (x : Vec 3)
    (hx : x ≠ 0) (hr : residual witnessA witnessB x ≠ 0) :
    projectionError witnessA witnessB x ^ 2 =
      (11 - x 0) ^ 2 / (normSq x + normSq (residual witnessA witnessB x)) +
      (6 - 36 * x 1) ^ 2 / (36 * normSq x + normSq (residual witnessA witnessB x)) +
      (5 - 25 * x 2) ^ 2 / (25 * normSq x + normSq (residual witnessA witnessB x)) := by
  let d : Vec 3 := ![normSq x + normSq (residual witnessA witnessB x),
    36 * normSq x + normSq (residual witnessA witnessB x),
    25 * normSq x + normSq (residual witnessA witnessB x)]
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    have hs := normSq_pos hx
    have ht := normSq_pos hr
    fin_cases i
    · change normSq x + normSq (residual witnessA witnessB x) ≠ 0
      linarith
    · change 36 * normSq x + normSq (residual witnessA witnessB x) ≠ 0
      linarith
    · change 25 * normSq x + normSq (residual witnessA witnessB x) ≠ 0
      linarith
  have hdiag : normSq x • (witnessA.transpose * witnessA) +
      normSq (residual witnessA witnessB x) • (1 : Mat 3 3) = Matrix.diagonal d := by
    rw [witness_gram]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [d, Matrix.diagonal_apply, Matrix.one_apply] <;> ring
  rw [projectionError_sq_formula _ _ _ hx hr, hdiag, inverse_diagonal_nonzero d hd]
  simp [realDot, witness_normalResidual, Matrix.mulVec_diagonal, d, Fin.sum_univ_succ]
  ring

theorem witness_projectionError_exact :
    projectionError witnessA witnessB witnessX1 ^ 2 =
      69694107852573439503892031925 / 69323394392991282508138323472 ∧
    projectionError witnessA witnessB witnessX2 ^ 2 =
      5430772101137459612205263871781350 / 5387955615790281743396033884265233 := by
  constructor
  · rw [witness_projection_formula _ witness_before_termination.1 witness_residuals_nonzero.1,
      witness_squared_lengths.1, witness_squared_lengths.2.1]
    norm_num [witnessX1]
  · rw [witness_projection_formula _ witness_before_termination.2.1 witness_residuals_nonzero.2,
      witness_squared_lengths.2.2.1, witness_squared_lengths.2.2.2]
    norm_num [witnessX2]

theorem witness_projectionError_separation :
    projectionError witnessA witnessB witnessX1 ^ 2 < 503 / 500 ∧
    (503 / 500 : ℝ) < 1007 / 1000 ∧
    (1007 / 1000 : ℝ) < projectionError witnessA witnessB witnessX2 ^ 2 := by
  rw [witness_projectionError_exact.1, witness_projectionError_exact.2]
  exact ⟨exact_cutoffs.2.1, exact_cutoffs.2.2.1, exact_cutoffs.2.2.2⟩

#assert_trust kernel projectionError_sq_formula
#assert_trust kernel witness_projectionError_exact
#print axioms projectionError_sq_formula

end NLA.IE17
