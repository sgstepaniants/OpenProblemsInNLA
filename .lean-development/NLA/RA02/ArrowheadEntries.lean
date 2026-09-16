/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Literal entries of the frozen arrowhead states and exact scalar corner algebra.
All ranks and finite active label sets remain symbolic.
-/
import NLA.RA02.Parameters
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

@[simp] lemma ordinary_ne_last {r : ℕ} (i : Fin r) :
    i.castSucc ≠ Fin.last r := ne_of_lt i.castSucc_lt_last

@[simp] lemma last_ne_ordinary {r : ℕ} (i : Fin r) :
    Fin.last r ≠ i.castSucc := Ne.symm (ordinary_ne_last i)

@[simp] lemma castSucc_mem_ordinaryLabels {r : ℕ} (U : Finset (Fin r)) (i : Fin r) :
    i.castSucc ∈ ordinaryLabels U ↔ i ∈ U := by
  simp [ordinaryLabels, Fin.castSucc_inj]

@[simp] lemma last_not_mem_ordinaryLabels {r : ℕ} (U : Finset (Fin r)) :
    Fin.last r ∉ ordinaryLabels U := by
  simp [ordinaryLabels]

lemma cornerValue_pos (r : ℕ) (U : Finset (Fin r)) : 0 < cornerValue r U := by
  apply add_pos_of_pos_of_nonneg (pow_pos (scaleParameter_pos r) r)
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (diagonalWeight_pos r i.val).le (sq_nonneg _)

lemma cornerValue_erase (r : ℕ) (U : Finset (Fin r)) (i : Fin r) (hi : i ∈ U) :
    cornerValue r U = cornerValue r (U.erase i) +
      diagonalWeight r i.val * couplingWeight r i.val ^ 2 := by
  unfold cornerValue
  rw [add_assoc, Finset.sum_erase_add _ _ hi]

@[simp] lemma state_true_ordinary (r : ℕ) (U : Finset (Fin r)) (i j : Fin r) :
    arrowheadState r U true i.castSucc j.castSucc =
      if i = j then (if i ∈ U then (diagonalWeight r i.val : ℂ) else 0) else 0 := by
  by_cases hi : i ∈ U <;> by_cases hj : j ∈ U <;> by_cases hij : i = j <;>
    simp_all [arrowheadState, Fin.castSucc_inj]

@[simp] lemma state_true_ordinary_last (r : ℕ) (U : Finset (Fin r)) (i : Fin r) :
    arrowheadState r U true i.castSucc (Fin.last r) =
      if i ∈ U then ((diagonalWeight r i.val * couplingWeight r i.val : ℝ) : ℂ) else 0 := by
  by_cases hi : i ∈ U <;> simp [arrowheadState, hi]

@[simp] lemma state_true_last_ordinary (r : ℕ) (U : Finset (Fin r)) (i : Fin r) :
    arrowheadState r U true (Fin.last r) i.castSucc =
      if i ∈ U then ((diagonalWeight r i.val * couplingWeight r i.val : ℝ) : ℂ) else 0 := by
  by_cases hi : i ∈ U <;> simp [arrowheadState, hi]

@[simp] lemma state_true_last_last (r : ℕ) (U : Finset (Fin r)) :
    arrowheadState r U true (Fin.last r) (Fin.last r) = (cornerValue r U : ℂ) := by
  simp [arrowheadState]

@[simp] lemma state_false_ordinary (r : ℕ) (U : Finset (Fin r)) (i j : Fin r) :
    arrowheadState r U false i.castSucc j.castSucc =
      if i ∈ U ∧ j ∈ U then
        (((if i = j then diagonalWeight r i.val else 0) -
          (diagonalWeight r i.val * couplingWeight r i.val) *
            (diagonalWeight r j.val * couplingWeight r j.val) / cornerValue r U : ℝ) : ℂ)
      else 0 := by
  by_cases hi : i ∈ U <;> by_cases hj : j ∈ U <;>
    simp [arrowheadState, hi, hj, Fin.castSucc_inj]

@[simp] lemma state_false_ordinary_last (r : ℕ) (U : Finset (Fin r)) (i : Fin r) :
    arrowheadState r U false i.castSucc (Fin.last r) = 0 := by
  simp [arrowheadState]

@[simp] lemma state_false_last_ordinary (r : ℕ) (U : Finset (Fin r)) (i : Fin r) :
    arrowheadState r U false (Fin.last r) i.castSucc = 0 := by
  simp [arrowheadState]

@[simp] lemma state_false_last_last (r : ℕ) (U : Finset (Fin r)) :
    arrowheadState r U false (Fin.last r) (Fin.last r) = 0 := by
  simp [arrowheadState]

@[simp] lemma state_false_last_row (r : ℕ) (U : Finset (Fin r)) (j : Fin (r + 1)) :
    arrowheadState r U false (Fin.last r) j = 0 := by
  simp [arrowheadState]

@[simp] lemma state_false_last_col (r : ℕ) (U : Finset (Fin r)) (i : Fin (r + 1)) :
    arrowheadState r U false i (Fin.last r) = 0 := by
  simp [arrowheadState]

lemma state_true_isHermitian (r : ℕ) (U : Finset (Fin r)) :
    (arrowheadState r U true).IsHermitian := by
  change (arrowheadState r U true)ᴴ = arrowheadState r U true
  ext i j
  change star (arrowheadState r U true j i) = arrowheadState r U true i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp
    · by_cases hj : j ∈ U <;> simp [hj]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · by_cases hi : i ∈ U <;> simp [hi]
    · by_cases hij : i = j
      · subst j
        by_cases hi : i ∈ U <;> simp [hi]
      · simp [hij, Ne.symm hij]

lemma state_true_diagonal (r : ℕ) (U : Finset (Fin r)) (i : Fin r) (hi : i ∈ U) :
    (arrowheadState r U true i.castSucc i.castSucc).re = diagonalWeight r i.val := by
  simp [hi]

lemma state_false_diagonal (r : ℕ) (U : Finset (Fin r)) (i : Fin r) (hi : i ∈ U) :
    (arrowheadState r U false i.castSucc i.castSucc).re =
      diagonalWeight r i.val * cornerValue r (U.erase i) / cornerValue r U := by
  have hc := cornerValue_erase r U i hi
  have hc0 := (cornerValue_pos r U).ne'
  simp only [state_false_ordinary, hi, and_self, if_true, if_pos rfl, Complex.ofReal_re]
  apply (eq_div_iff hc0).2
  field_simp [hc0]
  rw [hc]
  ring

#print axioms state_true_isHermitian
#assert_trust kernel state_true_isHermitian
#print axioms state_false_diagonal
#assert_trust kernel state_false_diagonal

end
end NLA.RA02
