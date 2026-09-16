/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

Complete rational LU factors for the literal witness. Before the target column
the lower factor is the source's band matrix. Its target column absorbs the
remaining residual; later columns are identity columns. No determinant or
trajectory assertion is part of these definitions.
-/
import NLA.IE13.WitnessForward
import NLA.IE13.TailAlgebra

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators
namespace NLA.IE13

def forwardPrefixSum (p q : ℕ) (i : Fin (witnessOrder p q)) : ℚ :=
  ∑ r : Fin (witnessOrder p q), if r.val < p + q then
    witnessLowerRational p q i r * forwardRational p r.val else 0

def fullLowerRational (p q : ℕ) : RatMat (witnessOrder p q) := fun i j =>
  if i = j then 1 else if j.val < p + q then witnessLowerRational p q i j
  else if j.val = p + q ∧ j < i then
    (targetFactorColumn p i.val - forwardPrefixSum p q i) / forwardRational p (p + q)
  else 0

def fullUpperRational (p q : ℕ) : RatMat (witnessOrder p q) := fun i j =>
  if j.val < p + q then witnessScale p * witnessUpperColumn p q j i
  else if j.val = p + q then (if i.val ≤ p + q then forwardRational p i.val else 0)
  else if i = j then 1 else 0

def fullLower (p q : ℕ) : Mat (witnessOrder p q) := fun i j => (fullLowerRational p q i j : ℂ)
def fullUpper (p q : ℕ) : Mat (witnessOrder p q) := fun i j => (fullUpperRational p q i j : ℂ)

lemma fullLower_rational_diag (p q : ℕ) (i : Fin (witnessOrder p q)) :
    fullLowerRational p q i i = 1 := by simp only [fullLowerRational, ite_true]

lemma fullLower_rational_prefix (p q : ℕ) (i j : Fin (witnessOrder p q))
    (hj : j.val < p + q) : fullLowerRational p q i j = witnessLowerRational p q i j := by
  by_cases he : i = j
  · subst i
    rw [fullLower_rational_diag, lower_rational_diag]
  · simp only [fullLowerRational, if_neg he, if_pos hj]

lemma fullLower_rational_above (p q : ℕ) (i j : Fin (witnessOrder p q)) (hij : i < j) :
    fullLowerRational p q i j = 0 := by
  rw [fullLowerRational, if_neg (ne_of_lt hij)]
  by_cases hj : j.val < p + q
  · rw [if_pos hj]
    exact lower_rational_above p q i j hij
  · rw [if_neg hj, if_neg (fun h => (not_lt_of_ge hij.le) h.2)]

lemma fullLower_rational_initial_row (p q : ℕ) (i : Fin (witnessOrder p q))
    (hi : i.val ≤ p + q) (r : Fin (witnessOrder p q)) :
    fullLowerRational p q i r = witnessLowerRational p q i r := by
  by_cases hr : r.val < p + q
  · exact fullLower_rational_prefix p q i r hr
  · by_cases hir : i = r
    · subst r
      rw [fullLower_rational_diag, lower_rational_diag]
    · have hilt : i < r := by
        have hne : i.val ≠ r.val := fun h => hir (Fin.ext h)
        change i.val < r.val
        omega
      rw [fullLower_rational_above p q i r hilt, lower_rational_above p q i r hilt]

lemma fullLower_rational_late (p q : ℕ) (i j : Fin (witnessOrder p q))
    (hj : p + q < j.val) : fullLowerRational p q i j = if i = j then 1 else 0 := by
  by_cases he : i = j
  · simp only [fullLowerRational, if_pos he]
  · simp only [fullLowerRational, if_neg he, if_neg (by omega : ¬j.val < p + q),
      if_neg (by omega : ¬(j.val = p + q ∧ j < i))]

lemma fullLower_target_below (p q : ℕ) (i : Fin (witnessOrder p q))
    (hi : p + q < i.val) :
    fullLowerRational p q i (witnessTarget p q) =
      (targetFactorColumn p i.val - forwardPrefixSum p q i) / forwardRational p (p + q) := by
  have hne : i ≠ witnessTarget p q := by
    intro he
    have hv := congrArg Fin.val he
    change i.val = p + q at hv
    omega
  have hcut : ¬(witnessTarget p q).val < p + q := by
    change ¬ (p + q < p + q)
    exact lt_irrefl (p + q)
  have htarget : (witnessTarget p q).val = p + q ∧ witnessTarget p q < i := by
    constructor
    · rfl
    · change p + q < i.val
      exact hi
  rw [fullLowerRational, if_neg hne, if_neg hcut, if_pos htarget]

lemma fullUpper_rational_above (p q : ℕ) (i j : Fin (witnessOrder p q)) (hji : j < i) :
    fullUpperRational p q i j = 0 := by
  unfold fullUpperRational
  by_cases hj : j.val < p + q
  · rw [if_pos hj, upper_column_below p q j i hji, mul_zero]
  · rw [if_neg hj]
    by_cases he : j.val = p + q
    · rw [if_pos he, if_neg (by have h := hji; change j.val < i.val at h; omega)]
    · rw [if_neg he, if_neg (ne_of_gt hji)]

lemma fullUpper_rational_diag_pos (p q : ℕ) (i : Fin (witnessOrder p q)) :
    0 < fullUpperRational p q i i := by
  unfold fullUpperRational
  by_cases hi : i.val < p + q
  · rw [if_pos hi]
    apply mul_pos
    · exact_mod_cast (witness_scale p).1
    · unfold witnessUpperColumn
      by_cases hip : i.val ≤ p
      · rw [if_pos hip]
        by_cases hi0 : i.val = 0
        · rw [if_pos hi0]
          norm_num
        · rw [if_neg hi0, if_pos le_rfl]
          positivity
      · rw [if_neg hip, if_pos rfl]
        norm_num
  · rw [if_neg hi]
    by_cases he : i.val = p + q
    · rw [if_pos he, if_pos (by omega : i.val ≤ p + q)]
      exact forwardRational_pos p i.val
    · rw [if_neg he, if_pos rfl]
      norm_num

lemma fullLower_triangular (p q : ℕ) : (fullLower p q).IsLowerTriangular := by
  intro i j hij
  change i < j at hij
  rw [fullLower, fullLower_rational_above p q i j hij, Rat.cast_zero]

lemma fullLower_diag (p q : ℕ) (i : Fin (witnessOrder p q)) : fullLower p q i i = 1 := by
  rw [fullLower, fullLower_rational_diag, Rat.cast_one]

lemma fullUpper_triangular (p q : ℕ) : (fullUpper p q).IsUpperTriangular := by
  intro i j hji
  change j < i at hji
  rw [fullUpper, fullUpper_rational_above p q i j hji, Rat.cast_zero]

lemma fullUpper_diag_ne_zero (p q : ℕ) (i : Fin (witnessOrder p q)) :
    fullUpper p q i i ≠ 0 := by
  unfold fullUpper
  exact_mod_cast (ne_of_gt (fullUpper_rational_diag_pos p q i))

lemma fullLower_prefix_norm (p q : ℕ) (k : Fin (witnessOrder p q))
    (hk : k.val < p + q) (i : Fin (witnessOrder p q)) : ‖fullLower p q i k‖ ≤ 1 := by
  rw [fullLower, fullLower_rational_prefix p q i k hk, Complex.norm_ratCast]
  exact_mod_cast lower_rational_abs p q i k

end NLA.IE13
