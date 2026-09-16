/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

The exact target-column forward substitution is the natural sharp recurrence.
A finite reindexing proves the all-order band convolution once.
-/
import NLA.IE13.WitnessColumns
import NLA.IE13.Recurrence
import Mathlib.Data.Rat.BigOperators

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators
namespace NLA.IE13

def forwardRational (p i : ℕ) : ℚ := if i = 0 then 1 else (bandSequence p i : ℚ)

def targetFactorColumn (p i : ℕ) : ℚ := if i = 0 then 1 else if i ≤ p then 0 else 1

lemma lower_window_reindex (p q : ℕ) (i : Fin (witnessOrder p q)) (f : ℕ → ℚ) :
    (∑ r : Fin (witnessOrder p q),
      if r.val < i.val ∧ i.val ≤ r.val + p then f r.val else 0) =
      ∑ s : Fin p, if s.val < i.val then f (i.val - 1 - s.val) else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  let S : Finset (Fin (witnessOrder p q)) :=
    Finset.univ.filter (fun r => r.val < i.val ∧ i.val ≤ r.val + p)
  let T : Finset (Fin p) := Finset.univ.filter (fun s => s.val < i.val)
  change (∑ r ∈ S, f r.val) = ∑ s ∈ T, f (i.val - 1 - s.val)
  have hS (r : Fin (witnessOrder p q)) (hr : r ∈ S) :
      r.val < i.val ∧ i.val ≤ r.val + p := (Finset.mem_filter.mp hr).2
  let g : ∀ r, r ∈ S → Fin p := fun r hr => ⟨i.val - 1 - r.val, by
    have hb := hS r hr
    omega⟩
  apply Finset.sum_bij g
  · intro r hr
    have hb := hS r hr
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, g, Fin.val_mk]
    omega
  · intro r hr s hs he
    have hbr := hS r hr
    have hbs := hS s hs
    have hv := congrArg Fin.val he
    dsimp only [g] at hv
    apply Fin.ext
    omega
  · intro s hs
    have hsi := (Finset.mem_filter.mp hs).2
    have hsp := s.isLt
    have hin := i.isLt
    let r : Fin (witnessOrder p q) := ⟨i.val - 1 - s.val, by omega⟩
    have hr : r ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, r, Fin.val_mk]
      omega
    refine ⟨r, hr, ?_⟩
    apply Fin.ext
    dsimp only [g, r]
    omega
  · intro r hr
    have hb := hS r hr
    congr 1
    dsimp only [g]
    omega

lemma forward_window (p i : ℕ) (hi : 0 < i) :
    (∑ s : Fin p, if s.val < i then forwardRational p (i - 1 - s.val) else 0) =
      (∑ s : Fin p, (bandSequence p (i - 1 - s.val) : ℚ)) +
        (if i ≤ p then 1 else 0) := by
  have hterm (s : Fin p) :
      (if s.val < i then forwardRational p (i - 1 - s.val) else 0) =
        (bandSequence p (i - 1 - s.val) : ℚ) + (if s.val + 1 = i then 1 else 0) := by
    by_cases he : s.val + 1 = i
    · have hsi : s.val < i := by omega
      have hz : i - 1 - s.val = 0 := by omega
      simp only [if_pos hsi, hz, forwardRational, ite_true,
        bandSequence_zero, Nat.cast_zero, if_pos he, zero_add]
    · by_cases hsi : s.val < i
      · have hn : i - 1 - s.val ≠ 0 := by omega
        simp only [if_pos hsi, forwardRational, if_neg hn, if_neg he, add_zero]
      · have hz : i - 1 - s.val = 0 := by omega
        simp only [if_neg hsi, hz, bandSequence_zero, Nat.cast_zero, if_neg he, add_zero]
  rw [Finset.sum_congr rfl (fun s _ => hterm s), Finset.sum_add_distrib]
  congr 1
  by_cases hip : i ≤ p
  · rw [if_pos hip]
    let a : Fin p := ⟨i - 1, by omega⟩
    have he (s : Fin p) : s.val + 1 = i ↔ s = a := by
      constructor
      · intro h
        apply Fin.ext
        dsimp only [a]
        omega
      · intro h
        subst s
        dsimp only [a]
        omega
    simp only [he, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · rw [if_neg hip]
    apply Finset.sum_eq_zero
    intro s _
    exact if_neg (by have hs := s.isLt; omega)

lemma forward_lower_action (p q : ℕ) (i : Fin (witnessOrder p q)) :
    (∑ r : Fin (witnessOrder p q),
      witnessLowerRational p q i r * forwardRational p r.val) = targetFactorColumn p i.val := by
  rw [lower_rational_action, lower_window_reindex]
  by_cases hi : i.val = 0
  · simp only [hi, forwardRational, targetFactorColumn, ite_true,
      Nat.not_lt_zero, if_false, Finset.sum_const_zero, sub_zero]
  · have hip : 0 < i.val := Nat.pos_of_ne_zero hi
    rw [forward_window p i.val hip, forwardRational, if_neg hi,
      targetFactorColumn, if_neg hi]
    have hr : (bandSequence p i.val : ℚ) =
        1 + ∑ s : Fin p, (bandSequence p (i.val - 1 - s.val) : ℚ) := by
      have he : i.val - 1 + 1 = i.val := by omega
      have hrec := (sequence_recurrence p).2 (i.val - 1)
      rw [he] at hrec
      exact_mod_cast hrec
    rw [hr]
    split_ifs <;> ring

lemma targetFactorColumn_original (p q : ℕ) (i : Fin (witnessOrder p q)) :
    targetFactorColumn p (witnessFactorIndex p q i).val = if p ≤ i.val then 1 else 0 := by
  by_cases hi : i.val < p
  · have hne : i.val + 1 ≠ 0 := by omega
    have hle : i.val + 1 ≤ p := by omega
    have hnot : ¬p ≤ i.val := by omega
    simp only [witnessFactorIndex, dif_pos hi, Fin.val_mk,
      targetFactorColumn, if_neg hne, if_pos hle, if_neg hnot]
  · by_cases he : i.val = p
    · have hle : p ≤ i.val := by omega
      simp only [witnessFactorIndex, dif_neg hi, if_pos he, Fin.val_mk,
        targetFactorColumn, ite_true, if_pos hle]
    · have hne : i.val ≠ 0 := by omega
      have hnot : ¬i.val ≤ p := by omega
      have hle : p ≤ i.val := by omega
      simp only [witnessFactorIndex, dif_neg hi, if_neg he,
        targetFactorColumn, if_neg hne, if_neg hnot, if_pos hle]

lemma forwardRational_pos (p i : ℕ) : 0 < forwardRational p i := by
  by_cases hi : i = 0
  · simp only [forwardRational, if_pos hi]
    norm_num
  · rw [forwardRational, if_neg hi]
    exact_mod_cast (sequence_properties p).2 i (Nat.pos_of_ne_zero hi)

#print axioms forward_lower_action
#assert_trust kernel forward_lower_action

end NLA.IE13
