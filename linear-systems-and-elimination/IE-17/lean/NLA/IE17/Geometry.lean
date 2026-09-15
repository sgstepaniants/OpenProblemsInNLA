/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Formalization: Department of Computing and Mathematical Sciences,
California Institute of Technology. Original counterexample: Matthew J. Colbrook.
-/
import NLA.IE17.Definitions
import LeanCert.Tactic.Verification

set_option autoImplicit false
open scoped BigOperators Classical Matrix.Norms.L2Operator
noncomputable section
namespace NLA.IE17

theorem euclideanNorm_sq {n : ℕ} (x : Vec n) : euclideanNorm x ^ 2 = normSq x := by
  exact EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)

theorem euclideanNorm_nonneg {n : ℕ} (x : Vec n) : 0 ≤ euclideanNorm x :=
  norm_nonneg _

theorem normSq_nonneg {n : ℕ} (x : Vec n) : 0 ≤ normSq x := by
  rw [← euclideanNorm_sq]
  exact sq_nonneg _

@[simp] theorem euclideanNorm_zero {n : ℕ} : euclideanNorm (0 : Vec n) = 0 := by
  simp [euclideanNorm]

@[simp] theorem normSq_zero {n : ℕ} : normSq (0 : Vec n) = 0 := by
  simp [normSq]

@[simp] theorem euclideanNorm_eq_zero {n : ℕ} (x : Vec n) :
    euclideanNorm x = 0 ↔ x = 0 := by
  simp [euclideanNorm]

theorem euclideanNorm_pos {n : ℕ} {x : Vec n} (hx : x ≠ 0) :
    0 < euclideanNorm x :=
  lt_of_le_of_ne (euclideanNorm_nonneg x) (Ne.symm ((euclideanNorm_eq_zero x).not.mpr hx))

theorem normSq_pos {n : ℕ} {x : Vec n} (hx : x ≠ 0) : 0 < normSq x := by
  rw [← euclideanNorm_sq]
  exact sq_pos_of_pos (euclideanNorm_pos hx)

theorem realDot_self {n : ℕ} (x : Vec n) : realDot x x = normSq x := by
  simp [realDot, normSq, pow_two]

theorem euclideanNorm_le_iff {n : ℕ} (x y : Vec n) :
    euclideanNorm x ≤ euclideanNorm y ↔ normSq x ≤ normSq y := by
  rw [← euclideanNorm_sq x, ← euclideanNorm_sq y]
  exact (sq_le_sq₀ (euclideanNorm_nonneg x) (euclideanNorm_nonneg y)).symm

theorem spectralNorm_nonneg {m n : ℕ} (E : Mat m n) : 0 ≤ spectralNorm E :=
  norm_nonneg _

@[simp] theorem spectralNorm_zero {m n : ℕ} : spectralNorm (0 : Mat m n) = 0 := by
  simp [spectralNorm]

theorem spectralNorm_transpose {m n : ℕ} (E : Mat m n) :
    spectralNorm E.transpose = spectralNorm E := by
  simpa only [spectralNorm, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.l2_opNorm_conjTranspose E

theorem euclideanNorm_mulVec_le {m n : ℕ} (E : Mat m n) (x : Vec n) :
    euclideanNorm (E.mulVec x) ≤ spectralNorm E * euclideanNorm x := by
  exact Matrix.l2_opNorm_mulVec E (WithLp.toLp 2 x)

theorem normSq_mulVec_le {m n : ℕ} (E : Mat m n) (x : Vec n) :
    normSq (E.mulVec x) ≤ spectralNorm E ^ 2 * normSq x := by
  have h := euclideanNorm_mulVec_le E x
  have hs := (sq_le_sq₀ (euclideanNorm_nonneg (E.mulVec x))
    (mul_nonneg (spectralNorm_nonneg E) (euclideanNorm_nonneg x))).mpr h
  simpa only [mul_pow, euclideanNorm_sq] using hs

theorem normSq_transpose_mulVec_le {m n : ℕ} (E : Mat m n) (x : Vec m) :
    normSq (E.transpose.mulVec x) ≤ spectralNorm E ^ 2 * normSq x := by
  simpa only [spectralNorm_transpose] using normSq_mulVec_le E.transpose x

theorem neg_self_feasible {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    FeasiblePerturbation A b x (-A) := by
  simp [FeasiblePerturbation]

theorem feasibleNorms_nonempty {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    (feasibleNorms A b x).Nonempty :=
  ⟨spectralNorm (-A), -A, neg_self_feasible A b x, rfl⟩

theorem feasibleNorms_bddBelow {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    BddBelow (feasibleNorms A b x) := by
  refine ⟨0, ?_⟩
  rintro c ⟨E, _, rfl⟩
  exact spectralNorm_nonneg E

theorem backwardError_nonneg {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    0 ≤ backwardError A b x := by
  apply le_csInf (feasibleNorms_nonempty A b x)
  rintro c ⟨E, _, rfl⟩
  exact spectralNorm_nonneg E

theorem backwardError_le {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n)
    (E : Mat m n) (hE : FeasiblePerturbation A b x E) :
    backwardError A b x ≤ spectralNorm E :=
  csInf_le (feasibleNorms_bddBelow A b x) ⟨E, hE, rfl⟩

theorem backwardError_zero_at_solution {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n)
    (hx : normalResidual A b x = 0) : backwardError A b x = 0 := by
  have hE : FeasiblePerturbation A b x 0 := by
    simpa [FeasiblePerturbation, normalResidual, residual, Matrix.mulVec_sub] using
      congrArg Neg.neg hx
  exact le_antisymm (by simpa using backwardError_le A b x 0 hE)
    (backwardError_nonneg A b x)

theorem projectionError_nonneg {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    0 ≤ projectionError A b x := by
  unfold projectionError
  split
  · exact le_rfl
  · exact div_nonneg (norm_nonneg _) (euclideanNorm_nonneg _)

#assert_trust kernel euclideanNorm_sq
#assert_trust kernel euclideanNorm_mulVec_le
#assert_trust kernel backwardError_zero_at_solution

end NLA.IE17
