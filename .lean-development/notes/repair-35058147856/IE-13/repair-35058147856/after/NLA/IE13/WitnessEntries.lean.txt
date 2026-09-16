/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

Literal rational witness entries in the original row order: exact band support,
unit input maximum and the required dimension. No factorization is assumed.
-/
import NLA.IE13.WitnessColumns
import NLA.IE13.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators
namespace NLA.IE13

lemma early_original_lower_support (p q : ℕ) (i j : Fin (witnessOrder p q))
    (hij : j.val + p < i.val) :
    (∑ r : Fin (witnessOrder p q),
      witnessLowerRational p q (witnessFactorIndex p q i) r * witnessUpperColumn p q j r) = 0 := by
  have hi : ¬i.val < p := by omega
  have hie : i.val ≠ p := by omega
  simp only [witnessFactorIndex, dif_neg hi, if_neg hie]
  exact lower_upper_below_band p q j i hij

lemma early_original_upper_support (p q : ℕ) (i j : Fin (witnessOrder p q))
    (hij : i.val < j.val) :
    (∑ r : Fin (witnessOrder p q),
      witnessLowerRational p q (witnessFactorIndex p q i) r * witnessUpperColumn p q j r) = 0 := by
  by_cases hj : j.val ≤ p
  · have hi : i.val < p := by omega
    apply lower_upper_initial_zero p q j (witnessFactorIndex p q i) hj
    · simp only [witnessFactorIndex, dif_pos hi, Fin.val_mk]
      omega
    · simp only [witnessFactorIndex, dif_pos hi, Fin.val_mk]
      omega
  · rw [lower_upper_late p q j _ (by omega)]
    apply lower_rational_above p q
    change (witnessFactorIndex p q i).val < j.val
    unfold witnessFactorIndex
    split_ifs <;> try simp only [Fin.val_mk]
    all_goals omega

lemma witness_rational_banded (p q : ℕ) (i j : Fin (witnessOrder p q))
    (hband : j.val + p < i.val ∨ i.val + q < j.val) : witnessRational p q i j = 0 := by
  by_cases hj : j.val < p + q
  · rw [witnessRational, if_pos hj]
    have hzero : (∑ r : Fin (witnessOrder p q),
        witnessLowerRational p q (witnessFactorIndex p q i) r * witnessUpperColumn p q j r) = 0 := by
      rcases hband with h | h
      · exact early_original_lower_support p q i j h
      · exact early_original_upper_support p q i j (by omega)
    rw [hzero, mul_zero]
  · rw [witnessRational, if_neg hj]
    by_cases hje : j.val = p + q
    · rw [if_pos hje]
      have hn : ¬p ≤ i.val := by
        intro hi
        have hin := i.isLt
        unfold witnessOrder at hin
        rcases hband with h | h <;> omega
      exact if_neg hn
    · rw [if_neg hje]
      have hne : i ≠ j := by
        intro he
        have hv := congrArg Fin.val he
        rcases hband with h | h <;> omega
      exact if_neg hne

lemma witness_rational_abs_le_one (p q : ℕ) (i j : Fin (witnessOrder p q)) :
    |witnessRational p q i j| ≤ 1 := by
  have hη : (0 : ℚ) < witnessScale p := by exact_mod_cast (witness_scale p).1
  have hη1 : witnessScale p ≤ (1 : ℚ) := by exact_mod_cast (witness_scale p).2.1
  have hηpow : witnessScale p * (2 : ℚ) ^ p = 1 := by exact_mod_cast (witness_scale p).2.2
  by_cases hj : j.val < p + q
  · rw [witnessRational, if_pos hj, abs_mul, abs_of_pos hη]
    by_cases hje : j.val ≤ p
    · calc
        witnessScale p * |∑ r : Fin (witnessOrder p q),
            witnessLowerRational p q (witnessFactorIndex p q i) r * witnessUpperColumn p q j r| ≤
            witnessScale p * (2 : ℚ) ^ j.val :=
          mul_le_mul_of_nonneg_left (lower_upper_abs_early p q j _ hje) hη.le
        _ ≤ witnessScale p * (2 : ℚ) ^ p :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hje) hη.le
        _ = 1 := hηpow
    · rw [lower_upper_late p q j _ (by omega)]
      exact (mul_le_mul_of_nonneg_left (lower_rational_abs p q _ _) hη.le).trans
        (by simpa only [mul_one] using hη1)
  · rw [witnessRational, if_neg hj]
    split_ifs <;> norm_num

lemma witness_entry_norm (p q : ℕ) (i j : Fin (witnessOrder p q)) :
    ‖witnessMatrix p q i j‖ ≤ 1 := by
  rw [witnessMatrix, Complex.norm_ratCast]
  exact_mod_cast witness_rational_abs_le_one p q i j

lemma witness_input_max (p q : ℕ) : entryMax (witnessMatrix p q) = 1 := by
  apply le_antisymm
  · rw [← activeMax_zero]
    exact activeMax_le (witnessMatrix p q) 0 1 (by norm_num)
      (fun i j _ _ => witness_entry_norm p q i j)
  · let i : Fin (witnessOrder p q) := ⟨p, by unfold witnessOrder; omega⟩
    let j := witnessTarget p q
    have he : witnessMatrix p q i j = 1 := by
      simp only [witnessMatrix, witnessRational, i, j, witnessTarget, Fin.val_mk,
        lt_self_iff_false, if_false, if_pos rfl, le_refl, if_true, Rat.cast_one]
    have hn := norm_le_entryMax (witnessMatrix p q) i j
    simpa only [he, norm_one] using hn

theorem witness_structure (p q : ℕ) (hp : 0 < p) :
    1 + max p q ≤ witnessOrder p q ∧
    Banded p q (witnessMatrix p q) ∧ entryMax (witnessMatrix p q) = 1 ∧
    ∀ i j : Fin (witnessOrder p q),
      ∃ r : ℚ, witnessMatrix p q i j = (r : ℂ) := by
  refine ⟨?_, ?_, witness_input_max p q, ?_⟩
  · have hm : max p q ≤ 2 * p + q := max_le (by omega) (by omega)
    unfold witnessOrder
    omega
  · intro i j h
    rw [witnessMatrix, witness_rational_banded p q i j h, Rat.cast_zero]
  · intro i j
    exact ⟨witnessRational p q i j, rfl⟩

#print axioms witness_structure
#assert_trust kernel witness_structure

end NLA.IE13
