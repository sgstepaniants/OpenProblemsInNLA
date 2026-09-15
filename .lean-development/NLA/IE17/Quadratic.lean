/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Quadratic identities and the bridge from a semidefinite Gram certificate to
the genuine Euclidean operator norm. No auxiliary norm is substituted.
-/
import NLA.IE17.ProjectionAlgebra
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical Matrix.Norms.L2Operator
noncomputable section
namespace NLA.IE17

theorem realDot_comm {n : ℕ} (x y : Vec n) : realDot x y = realDot y x :=
  dotProduct_comm x y

theorem realDot_add {n : ℕ} (x y z : Vec n) :
    realDot x (y + z) = realDot x y + realDot x z := by
  simp [realDot, mul_add, Finset.sum_add_distrib]

theorem realDot_sub {n : ℕ} (x y z : Vec n) :
    realDot x (y - z) = realDot x y - realDot x z := by
  simp [realDot, mul_sub, Finset.sum_sub_distrib]

theorem realDot_smul {n : ℕ} (x y : Vec n) (a : ℝ) :
    realDot x (a • y) = a * realDot x y := by
  simp [realDot, Finset.mul_sum, mul_left_comm]

theorem outer_mulVec {m n : ℕ} (x : Vec m) (y z : Vec n) :
    (outer x y).mulVec z = realDot y z • x := by
  ext i
  simp [outer, realDot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm]

theorem realDot_outer {n : ℕ} (x y : Vec n) :
    realDot x ((outer y y).mulVec x) = realDot x y ^ 2 := by
  rw [outer_mulVec, realDot_smul, realDot_comm y x, pow_two]

theorem normSq_neg {n : ℕ} (x : Vec n) : normSq (-x) = normSq x := by
  simp [normSq]

theorem normSq_sub {n : ℕ} (x y : Vec n) :
    normSq (x - y) = normSq x + normSq y - 2 * realDot x y := by
  calc
    _ = ∑ i, ((x i) ^ 2 + (y i) ^ 2 - 2 * (x i * y i)) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp
      ring
    _ = _ := by simp [normSq, realDot, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.mul_sum]

theorem realDot_gram {m n : ℕ} (M : Mat m n) (x : Vec n) :
    realDot x ((M.transpose * M).mulVec x) = normSq (M.mulVec x) := by
  rw [← realDot_self]
  rw [← Matrix.mulVec_mulVec]
  exact (dot_mulVec_left M x (M.mulVec x)).symm

theorem realDot_cogram {m n : ℕ} (M : Mat m n) (x : Vec m) :
    realDot x ((M * M.transpose).mulVec x) = normSq (M.transpose.mulVec x) := by
  simpa only [Matrix.transpose_transpose] using realDot_gram M.transpose x

theorem realDot_gram_complement {m n : ℕ} (M : Mat m n) (c : ℝ) (x : Vec n) :
    realDot x ((c • (1 : Mat n n) - M.transpose * M).mulVec x) =
      c * normSq x - normSq (M.mulVec x) := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    realDot_sub, realDot_smul, realDot_self, realDot_gram]

theorem spectralNorm_sq_le_of_gram_posSemidef {m n : ℕ} (M : Mat m n) (c : ℝ)
    (hc : 0 ≤ c) (hM : (c • (1 : Mat n n) - M.transpose * M).PosSemidef) :
    spectralNorm M ^ 2 ≤ c := by
  have hquad : ∀ x : Vec n, normSq (M.mulVec x) ≤ c * normSq x := by
    intro x
    have h := hM.dotProduct_mulVec_nonneg x
    have h' : 0 ≤ realDot x ((c • (1 : Mat n n) - M.transpose * M).mulVec x) := by
      simpa only [star_trivial] using h
    rw [realDot_gram_complement] at h'
    linarith
  have hvec : ∀ x : Vec n,
      euclideanNorm (M.mulVec x) ≤ Real.sqrt c * euclideanNorm x := by
    intro x
    apply (sq_le_sq₀ (euclideanNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (euclideanNorm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hc, euclideanNorm_sq, euclideanNorm_sq]
    exact hquad x
  let f : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap) M
  have hf : ‖f‖ ≤ Real.sqrt c := by
    apply f.opNorm_le_bound (Real.sqrt_nonneg c)
    intro x
    exact hvec (WithLp.ofLp x)
  have hs : spectralNorm M ≤ Real.sqrt c := hf
  have hsSq := (sq_le_sq₀ (spectralNorm_nonneg M) (Real.sqrt_nonneg c)).mpr hs
  simpa only [Real.sq_sqrt hc] using hsSq

#assert_trust kernel spectralNorm_sq_le_of_gram_posSemidef
#print axioms spectralNorm_sq_le_of_gram_posSemidef

end NLA.IE17
