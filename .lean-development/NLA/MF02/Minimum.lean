/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
An attained finite stage minimum, with uniform constants for every budget.
-/
import NLA.MF02.Bounds

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF02

lemma budget_stage_admissible (m : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    cubicError m δ ≤ unrestrictedError m δ :=
  (cubicError_upper_bound m hm δ hδ0 hδ1).trans
    (unrestrictedError_lower_bound m δ hδ0 hδ1)

lemma first_stage_admissible_small (m : ℕ) (hm : m ≤ 1)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    cubicError 1 δ ≤ unrestrictedError m δ := by
  rw [unrestrictedError_eq_gapRatio_of_le_one m hm δ hδ0 hδ1]
  have hr0 := gapRatio_pos hδ0 hδ1
  have hr1 := gapRatio_lt_one hδ0
  have hu := cubicError_upper_bound 1 (by decide) δ hδ0 hδ1
  norm_num at hu
  nlinarith

lemma admissible_stage_exists (m : ℕ) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ T : ℕ, cubicError T δ ≤ unrestrictedError m δ := by
  by_cases hm : m = 0
  · subst m
    exact ⟨1, first_stage_admissible_small 0 (by decide) δ hδ0 hδ1⟩
  · exact ⟨m, budget_stage_admissible m (by omega) δ hδ0 hδ1⟩

lemma stageMinimum_le_of_admissible (m T : ℕ) (δ : ℝ)
    (hT : cubicError T δ ≤ unrestrictedError m δ) :
    stageMinimum m δ ≤ (T : WithTop ℕ) := by
  unfold stageMinimum
  exact sInf_le ⟨T, hT, rfl⟩

theorem stage_minimum_attained (m : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ T : ℕ, stageMinimum m δ = (T : WithTop ℕ) ∧
      cubicError T δ ≤ unrestrictedError m δ ∧
      ∀ S : ℕ, S < T → unrestrictedError m δ < cubicError S δ := by
  classical
  have hex := admissible_stage_exists m δ hδ0 hδ1
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex, ?_⟩
  · apply le_antisymm
    · exact stageMinimum_le_of_admissible m (Nat.find hex) δ (Nat.find_spec hex)
    · unfold stageMinimum
      apply le_sInf
      rintro y ⟨S, hS, rfl⟩
      exact WithTop.coe_le_coe.mpr (Nat.find_min' hex hS)
  · intro S hS
    exact lt_of_not_ge (Nat.find_min hex hS)

lemma stageMinimum_eq_one (m : ℕ) (δ : ℝ)
    (hzero : unrestrictedError m δ < cubicError 0 δ)
    (hone : cubicError 1 δ ≤ unrestrictedError m δ) : stageMinimum m δ = 1 := by
  apply le_antisymm
  · exact stageMinimum_le_of_admissible m 1 δ hone
  · unfold stageMinimum
    apply le_sInf
    rintro y ⟨S, hS, rfl⟩
    have hSzero : S ≠ 0 := by
      intro h
      subst S
      exact (not_lt_of_ge hS) hzero
    exact WithTop.coe_le_coe.mpr (show 1 ≤ S by omega)

lemma stageMinimum_eq_one_of_le_one (m : ℕ) (hm : m ≤ 1)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) : stageMinimum m δ = 1 := by
  apply stageMinimum_eq_one
  · rw [unrestrictedError_eq_gapRatio_of_le_one m hm δ hδ0 hδ1,
      cubicError_zero hδ0 hδ1]
    unfold gapRatio
    apply (div_lt_iff₀ (show 0 < 1 + δ by linarith)).mpr
    nlinarith
  · exact first_stage_admissible_small m hm δ hδ0 hδ1

theorem stage_minimum_small_budgets (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    stageMinimum 0 δ = 1 ∧ stageMinimum 1 δ = 1 :=
  ⟨stageMinimum_eq_one_of_le_one 0 (by decide) δ hδ0 hδ1,
    stageMinimum_eq_one_of_le_one 1 (by decide) δ hδ0 hδ1⟩

theorem stage_minimum_bounds (m : ℕ) (hm : 2 ≤ m)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ((m / 2 : ℕ) : WithTop ℕ) ≤ stageMinimum m δ ∧
    stageMinimum m δ ≤ (m : WithTop ℕ) := by
  constructor
  · unfold stageMinimum
    apply le_sInf
    rintro y ⟨S, hS, rfl⟩
    apply WithTop.coe_le_coe.mpr
    by_contra hnot
    have hSk : S < m / 2 := lt_of_not_ge hnot
    have hstrict := cubic_error_strictly_decreases δ hδ0 hδ1 hSk
    have hcost := unrestrictedError_le_cubicError m (m / 2) (by omega) δ hδ0 hδ1
    exact (not_lt_of_ge (hS.trans hcost)) hstrict
  · exact stageMinimum_le_of_admissible m m δ
      (budget_stage_admissible m (by omega) δ hδ0 hδ1)

theorem uniform_asymptotic_order (m : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ T : ℕ, stageMinimum m δ = (T : WithTop ℕ) ∧
      ((m : ℝ) + 1) / 4 ≤ (T : ℝ) ∧ (T : ℝ) ≤ (m : ℝ) + 1 := by
  by_cases hm : m < 2
  · have heq := stageMinimum_eq_one_of_le_one m (by omega) δ hδ0 hδ1
    refine ⟨1, heq, ?_, ?_⟩
    · have hreal : (m : ℝ) ≤ 1 := by exact_mod_cast (show m ≤ 1 by omega)
      change ((m : ℝ) + 1) / 4 ≤ 1
      linarith
    · have hnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      change (1 : ℝ) ≤ (m : ℝ) + 1
      linarith
  · have hm2 : 2 ≤ m := by omega
    obtain ⟨T, heq, hT, hminimal⟩ := stage_minimum_attained m δ hδ0 hδ1
    have hb := stage_minimum_bounds m hm2 δ hδ0 hδ1
    rw [heq] at hb
    have hlow : m / 2 ≤ T := WithTop.coe_le_coe.mp hb.1
    have hupp : T ≤ m := WithTop.coe_le_coe.mp hb.2
    have hfour : m + 1 ≤ 4 * T := by omega
    have hfourR : (m : ℝ) + 1 ≤ 4 * (T : ℝ) := by exact_mod_cast hfour
    have huppR : (T : ℝ) ≤ (m : ℝ) := by exact_mod_cast hupp
    refine ⟨T, heq, ?_, ?_⟩ <;> linarith

#assert_trust kernel stage_minimum_attained
#print axioms stage_minimum_attained
#assert_trust kernel stage_minimum_small_budgets
#print axioms stage_minimum_small_budgets
#assert_trust kernel stage_minimum_bounds
#print axioms stage_minimum_bounds
#assert_trust kernel uniform_asymptotic_order
#print axioms uniform_asymptotic_order

end NLA.MF02
