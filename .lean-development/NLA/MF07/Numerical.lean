/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Only exp(1) <= 3 is interval certified. Dimension, word length, threshold,
and every power and denominator identity remain symbolic.
-/
import NLA.MF07.Definitions
import Mathlib.Tactic
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF07

theorem exp_one_bound : Real.exp 1 ≤ 3 := by
  interval_decide (trust := kernel)

lemma variable_binomial_bound (m n : ℕ) (hn : 1 ≤ n) :
    (1 + (m : ℝ) / (n : ℝ)) ^ n ≤ (3 : ℝ) ^ m := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hb : 1 + (m : ℝ) / (n : ℝ) ≤ Real.exp ((m : ℝ) / (n : ℝ)) := by
    simpa only [add_comm] using Real.add_one_le_exp ((m : ℝ) / (n : ℝ))
  calc
    (1 + (m : ℝ) / (n : ℝ)) ^ n ≤
        (Real.exp ((m : ℝ) / (n : ℝ))) ^ n :=
      pow_le_pow_left₀ (by positivity) hb n
    _ = Real.exp (m : ℝ) := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    _ = (Real.exp 1) ^ m := by simpa using Real.exp_nat_mul 1 m
    _ ≤ (3 : ℝ) ^ m := pow_le_pow_left₀ (Real.exp_pos 1).le exp_one_bound m

lemma comparisonThreshold_ge_one (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (L : ℝ) (hL : 1 ≤ L) : 1 ≤ comparisonThreshold d n L := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : (0 : ℝ) < ((d-1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < d-1 by omega)
  have hmd : ((d-1 : ℕ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.sub_le d 1
  have hD : 0 ≤ 2 * (d : ℝ)^2 := by positivity
  have hDL : 2 * (d : ℝ)^2 ≤ 2 * (d : ℝ)^2 * L := by nlinarith
  have hDL0 : 0 ≤ 2 * (d : ℝ)^2 * L := by positivity
  have hDLN : 2 * (d : ℝ)^2 * L ≤ 2 * (d : ℝ)^2 * L * (n : ℝ) := by
    nlinarith
  unfold comparisonThreshold
  apply (le_div_iff₀ hm).2
  nlinarith

lemma comparisonThreshold_ratio (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (L : ℝ) (hL : 1 ≤ L) :
    2 * (d : ℝ)^2 * L / comparisonThreshold d n L =
      ((d-1 : ℕ) : ℝ) / (n : ℝ) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hL0 : L ≠ 0 := by linarith
  have hm0 : ((d-1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (show d-1 ≠ 0 by omega)
  unfold comparisonThreshold
  field_simp

theorem comparison_threshold_bound (d n : ℕ) (hd : 2 ≤ d) (hn : 1 ≤ n)
    (L : ℝ) (hL : 1 ≤ L) :
    1 ≤ comparisonThreshold d n L ∧
    (d : ℝ) * comparisonThreshold d n L ^ (d - 1) *
      (1 + 2 * (d : ℝ) ^ 2 * L / comparisonThreshold d n L) ^ n ≤
      growthConstant d * (L * (n : ℝ)) ^ (d - 1) := by
  have hs := comparisonThreshold_ge_one d n hd hn L hL
  refine ⟨hs, ?_⟩
  rw [comparisonThreshold_ratio d n hd hn L hL]
  calc
    (d : ℝ) * comparisonThreshold d n L ^ (d-1) *
        (1 + ((d-1 : ℕ) : ℝ) / (n : ℝ)) ^ n ≤
        (d : ℝ) * comparisonThreshold d n L ^ (d-1) * 3 ^ (d-1) :=
      mul_le_mul_of_nonneg_left (variable_binomial_bound (d-1) n hn)
        (mul_nonneg (Nat.cast_nonneg d) (pow_nonneg (by linarith) _))
    _ = growthConstant d * (L * (n : ℝ)) ^ (d-1) := by
      rw [growthConstant, if_neg (by omega)]
      unfold comparisonThreshold
      rw [mul_assoc, ← mul_pow]
      have hid : 2 * (d : ℝ)^2 * L * (n : ℝ) / ((d-1 : ℕ) : ℝ) * 3 =
          (6 * (d : ℝ)^2 / ((d-1 : ℕ) : ℝ)) * (L * (n : ℝ)) := by ring
      rw [hid, mul_pow]
      ring

theorem growth_constant_positive (d : ℕ) (hd : 1 ≤ d) :
    0 < growthConstant d := by
  unfold growthConstant
  split_ifs with h
  · norm_num
  · have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hm0 : (0 : ℝ) < ((d-1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < d-1 by omega)
    positivity

#print axioms exp_one_bound
#assert_trust kernel exp_one_bound
#print axioms variable_binomial_bound
#assert_trust kernel variable_binomial_bound
#print axioms comparison_threshold_bound
#assert_trust kernel comparison_threshold_bound
#print axioms growth_constant_positive
#assert_trust kernel growth_constant_positive

end NLA.MF07
