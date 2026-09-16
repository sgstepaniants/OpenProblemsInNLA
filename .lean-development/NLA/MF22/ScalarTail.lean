/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

An exact qualitative geometric-growth argument controls the normalized
boundary denominator uniformly in all sufficiently large indices. No index
search, truncated tail, or approximate complex eigenvalue is used.
-/
import NLA.MF22.Norms
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open Filter

lemma norm_ge_half_of_close_to_one (d : ℂ) (h : ‖d - 1‖ ≤ (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) ≤ ‖d‖ := by
  have he := norm_sub_norm_le (1 : ℂ) d
  rw [norm_one, norm_sub_rev] at he
  linarith

lemma inverse_error_of_close_to_one (d : ℂ) (h : (1 / 2 : ℝ) ≤ ‖d‖) :
    ‖1 - d⁻¹‖ ≤ 2 * ‖d - 1‖ := by
  have hd : d ≠ 0 := by intro he; simp [he] at h
  have he : 1 - d⁻¹ = (d - 1) / d := by field_simp [hd]
  rw [he, norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hd)).mpr
  nlinarith [norm_nonneg (d - 1)]

lemma scalar_dominant_tail (γ μ : ℂ) (hγ : γ ≠ 0) (hμ : 1 < ‖μ‖)
    (r : ℕ → ℂ) (C : ℝ) (hC : 0 < C) (hr : ∀ n : ℕ, ‖r n‖ ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      γ * μ ^ n + r n ≠ 0 ∧
      (1 / 2 : ℝ) ≤ ‖(γ * μ ^ n + r n) / (γ * μ ^ n)‖ ∧
      ‖1 - ((γ * μ ^ n + r n) / (γ * μ ^ n))⁻¹‖ ≤
        D * (‖μ‖ ^ n)⁻¹ := by
  have hg : 0 < ‖γ‖ := norm_pos_iff.mpr hγ
  have hl : 0 < ‖μ‖ := lt_trans zero_lt_one hμ
  have hlne : μ ≠ 0 := norm_pos_iff.mp hl
  have hevent : ∀ᶠ n : ℕ in atTop, 2 * C / ‖γ‖ ≤ ‖μ‖ ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hμ).eventually_ge_atTop _
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  refine ⟨2 * C / ‖γ‖, div_pos (mul_pos (by norm_num) hC) hg,
    max 1 N, le_max_left _ _, ?_⟩
  intro n hn
  have hpow := hN n (le_trans (le_max_right _ _) hn)
  have hgn : γ * μ ^ n ≠ 0 := mul_ne_zero hγ (pow_ne_zero n hlne)
  have hpos : 0 < ‖γ‖ * ‖μ‖ ^ n := mul_pos hg (pow_pos hl n)
  let d : ℂ := (γ * μ ^ n + r n) / (γ * μ ^ n)
  have hdifference : d - 1 = r n / (γ * μ ^ n) := by
    dsimp [d]
    field_simp [hgn]
  have herror : ‖d - 1‖ ≤ C / (‖γ‖ * ‖μ‖ ^ n) := by
    rw [hdifference, norm_div, norm_mul, norm_pow]
    exact div_le_div_of_nonneg_right (hr n) hpos.le
  have hhalf : ‖d - 1‖ ≤ (1 / 2 : ℝ) := by
    apply herror.trans
    apply (div_le_iff₀ hpos).mpr
    have hc := (div_le_iff₀ hg).mp hpow
    nlinarith
  have hdnorm := norm_ge_half_of_close_to_one d hhalf
  refine ⟨?_, hdnorm, ?_⟩
  · intro ha
    have hd0 : d = 0 := by simp [d, ha]
    rw [hd0, norm_zero] at hdnorm
    norm_num at hdnorm
  · calc
      ‖1 - d⁻¹‖ ≤ 2 * ‖d - 1‖ := inverse_error_of_close_to_one d hdnorm
      _ ≤ 2 * (C / (‖γ‖ * ‖μ‖ ^ n)) :=
        mul_le_mul_of_nonneg_left herror (by norm_num)
      _ = (2 * C / ‖γ‖) * (‖μ‖ ^ n)⁻¹ := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring

#assert_trust kernel scalar_dominant_tail
#print axioms scalar_dominant_tail

end NLA.MF22
