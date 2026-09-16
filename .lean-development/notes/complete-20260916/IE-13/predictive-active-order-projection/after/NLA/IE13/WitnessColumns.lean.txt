/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

Exact rational column algebra. Finite geometric sums replace expansion of any
concrete matrix; p, q and the matrix order remain arbitrary throughout.
-/
import NLA.IE13.WitnessScale
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators
namespace NLA.IE13

def geometricEntry (r : ℕ) : ℚ := if r = 0 then 1 else 2 ^ (r - 1)

lemma geometricEntry_nonneg (r : ℕ) : 0 ≤ geometricEntry r := by
  unfold geometricEntry
  split_ifs <;> positivity

lemma geometric_prefix (m : ℕ) :
    (∑ r ∈ Finset.range (m + 1), geometricEntry r) = (2 : ℚ) ^ m := by
  induction m with
  | zero => norm_num [geometricEntry]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have he : geometricEntry (m + 1) = (2 : ℚ) ^ m := by simp [geometricEntry]
    rw [he, pow_succ]
    ring

lemma sum_fin_prefix {n : ℕ} (f : ℕ → ℚ) (m : ℕ) (hm : m ≤ n) :
    (∑ r : Fin n, if r.val < m then f r.val else 0) = ∑ r ∈ Finset.range m, f r := by
  calc
    (∑ r : Fin n, if r.val < m then f r.val else 0) =
        ∑ r ∈ Finset.range n, if r < m then f r else 0 :=
      (Finset.sum_range (fun r : ℕ => if r < m then f r else 0)).symm
    _ = ∑ r ∈ Finset.range m, if r < m then f r else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hm)
      intro r hr hrm
      exact if_neg (fun h => hrm (Finset.mem_range.mpr h))
    _ = ∑ r ∈ Finset.range m, f r :=
      Finset.sum_congr rfl (fun r hr => if_pos (Finset.mem_range.mp hr))

lemma lower_rational_diag (p q : ℕ) (i : Fin (witnessOrder p q)) :
    witnessLowerRational p q i i = 1 := by simp [witnessLowerRational]

lemma lower_rational_abs (p q : ℕ) (i j : Fin (witnessOrder p q)) :
    |witnessLowerRational p q i j| ≤ 1 := by
  unfold witnessLowerRational
  split_ifs <;> norm_num

lemma lower_rational_above (p q : ℕ) (i j : Fin (witnessOrder p q)) (hij : i < j) :
    witnessLowerRational p q i j = 0 := by
  have hn : ¬j.val < i.val := by have h := hij; change i.val < j.val at h; omega
  simp only [witnessLowerRational, if_neg (ne_of_lt hij), hn, false_and, if_false]

lemma lower_rational_action (p q : ℕ) (u : Fin (witnessOrder p q) → ℚ)
    (i : Fin (witnessOrder p q)) :
    (∑ r : Fin (witnessOrder p q), witnessLowerRational p q i r * u r) =
      u i - ∑ r : Fin (witnessOrder p q),
        if r.val < i.val ∧ i.val ≤ r.val + p then u r else 0 := by
  have hterm (r : Fin (witnessOrder p q)) : witnessLowerRational p q i r * u r =
      (if r = i then u i else 0) -
        (if r.val < i.val ∧ i.val ≤ r.val + p then u r else 0) := by
    by_cases hri : r = i
    · subst r
      simp [witnessLowerRational]
    · simp only [witnessLowerRational, if_neg (Ne.symm hri), if_neg hri]
      split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun r _ => hterm r), Finset.sum_sub_distrib]
  simp

lemma upper_column_early (p q : ℕ) (j r : Fin (witnessOrder p q)) (hj : j.val ≤ p) :
    witnessUpperColumn p q j r = if r.val ≤ j.val then geometricEntry r.val else 0 := by
  simp only [witnessUpperColumn, if_pos hj, geometricEntry]
  by_cases hr : r.val = 0
  · simp only [if_pos hr, hr, Nat.zero_le, if_true]
  · simp only [if_neg hr]

lemma upper_column_nonneg (p q : ℕ) (j r : Fin (witnessOrder p q)) :
    0 ≤ witnessUpperColumn p q j r := by
  unfold witnessUpperColumn
  split_ifs <;> positivity

lemma upper_column_below (p q : ℕ) (j r : Fin (witnessOrder p q)) (hjr : j < r) :
    witnessUpperColumn p q j r = 0 := by
  by_cases hj : j.val ≤ p
  · rw [upper_column_early p q j r hj]
    exact if_neg (by have h := hjr; change j.val < r.val at h; omega)
  · simp only [witnessUpperColumn, if_neg hj, if_neg (ne_of_gt hjr)]

lemma upper_column_sum_early (p q : ℕ) (j : Fin (witnessOrder p q)) (hj : j.val ≤ p) :
    (∑ r : Fin (witnessOrder p q), witnessUpperColumn p q j r) = (2 : ℚ) ^ j.val := by
  have he : (∑ r : Fin (witnessOrder p q), witnessUpperColumn p q j r) =
      ∑ r : Fin (witnessOrder p q), if r.val < j.val + 1 then geometricEntry r.val else 0 := by
    apply Finset.sum_congr rfl
    intro r _
    rw [upper_column_early p q j r hj]
    have hiff : r.val ≤ j.val ↔ r.val < j.val + 1 := by omega
    rw [hiff]
  rw [he, sum_fin_prefix geometricEntry (j.val + 1) (Nat.succ_le_of_lt j.isLt), geometric_prefix]

lemma lower_upper_late (p q : ℕ) (j i : Fin (witnessOrder p q)) (hj : p < j.val) :
    (∑ r : Fin (witnessOrder p q),
      witnessLowerRational p q i r * witnessUpperColumn p q j r) =
        witnessLowerRational p q i j := by
  simp only [witnessUpperColumn, if_neg (by omega : ¬j.val ≤ p)]
  simp

lemma lower_upper_initial_zero (p q : ℕ) (j i : Fin (witnessOrder p q))
    (hj : j.val ≤ p) (hi : 0 < i.val) (hij : i.val ≤ j.val) :
    (∑ r : Fin (witnessOrder p q),
      witnessLowerRational p q i r * witnessUpperColumn p q j r) = 0 := by
  rw [lower_rational_action]
  have hs : (∑ r : Fin (witnessOrder p q),
      if r.val < i.val ∧ i.val ≤ r.val + p then witnessUpperColumn p q j r else 0) =
        ∑ r : Fin (witnessOrder p q), if r.val < i.val then geometricEntry r.val else 0 := by
    apply Finset.sum_congr rfl
    intro r _
    by_cases hr : r.val < i.val
    · rw [if_pos ⟨hr, by omega⟩, if_pos hr, upper_column_early p q j r hj,
        if_pos (by omega : r.val ≤ j.val)]
    · rw [if_neg (fun h => hr h.1), if_neg hr]
  rw [hs, sum_fin_prefix geometricEntry i.val i.isLt.le,
    upper_column_early p q j i hj, if_pos hij]
  have hgeom : (∑ r ∈ Finset.range i.val, geometricEntry r) = (2 : ℚ) ^ (i.val - 1) := by
    have he : i.val - 1 + 1 = i.val := by omega
    simpa only [he] using geometric_prefix (i.val - 1)
  rw [hgeom, geometricEntry, if_neg (by omega : i.val ≠ 0)]
  ring

lemma lower_upper_below_band (p q : ℕ) (j i : Fin (witnessOrder p q))
    (hij : j.val + p < i.val) :
    (∑ r : Fin (witnessOrder p q),
      witnessLowerRational p q i r * witnessUpperColumn p q j r) = 0 := by
  apply Finset.sum_eq_zero
  intro r _
  by_cases hr : r.val ≤ j.val
  · have hir : i ≠ r := by intro h; have hv := congrArg Fin.val h; omega
    have hb : ¬(r.val < i.val ∧ i.val ≤ r.val + p) := by omega
    simp only [witnessLowerRational, if_neg hir, if_neg hb, zero_mul]
  · rw [upper_column_below p q j r (by change j.val < r.val; omega), mul_zero]

lemma lower_upper_abs_early (p q : ℕ) (j i : Fin (witnessOrder p q)) (hj : j.val ≤ p) :
    |∑ r : Fin (witnessOrder p q),
      witnessLowerRational p q i r * witnessUpperColumn p q j r| ≤ (2 : ℚ) ^ j.val := by
  calc
    |∑ r : Fin (witnessOrder p q),
        witnessLowerRational p q i r * witnessUpperColumn p q j r| ≤
        ∑ r : Fin (witnessOrder p q),
          |witnessLowerRational p q i r * witnessUpperColumn p q j r| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin (witnessOrder p q), witnessUpperColumn p q j r := by
      apply Finset.sum_le_sum
      intro r _
      rw [abs_mul, abs_of_nonneg (upper_column_nonneg p q j r)]
      exact (mul_le_mul_of_nonneg_right (lower_rational_abs p q i r)
        (upper_column_nonneg p q j r)).trans_eq (one_mul _)
    _ = (2 : ℚ) ^ j.val := upper_column_sum_early p q j hj

end NLA.IE13
