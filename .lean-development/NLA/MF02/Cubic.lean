/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Chen-Chow cubic interval control by exact positive-factor identities.
-/
import NLA.MF02.Definitions
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF02
open Polynomial

noncomputable def criticalPoint (a : ℝ) : ℝ :=
  Real.sqrt (cubicA a) / Real.sqrt 3

lemma cubicA_pos {a : ℝ} (ha : 0 < a) : 0 < cubicA a := by
  unfold cubicA
  positivity

lemma criticalPoint_data {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < criticalPoint a ∧ cubicA a = 3 * criticalPoint a ^ 2 ∧
    cubicScale a = 2 * criticalPoint a ^ 3 ∧
    a < criticalPoint a ∧ criticalPoint a < 1 := by
  have hA := cubicA_pos ha0
  have hroot := Real.sqrt_pos.mpr hA
  have hroot3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsA := Real.sq_sqrt hA.le
  have hs3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have ht : 0 < criticalPoint a := div_pos hroot hroot3
  have hAt : cubicA a = 3 * criticalPoint a ^ 2 := by
    unfold criticalPoint
    rw [div_pow, hsA, hs3]
    ring
  have hMt : cubicScale a = 2 * criticalPoint a ^ 3 := by
    calc
      cubicScale a = (2 * cubicA a / 3) * criticalPoint a := by
        unfold cubicScale criticalPoint
        ring
      _ = 2 * criticalPoint a ^ 3 := by rw [hAt]; ring
  have hlow : 3 * a ^ 2 < cubicA a := by
    have h := mul_pos (sub_pos.mpr ha1) (show 0 < 1 + 2 * a by linarith)
    dsimp [cubicA]
    nlinarith
  have hhigh : cubicA a < 3 := by
    have h := mul_pos (sub_pos.mpr ha1) (show 0 < a + 2 by linarith)
    dsimp [cubicA]
    nlinarith
  exact ⟨ht, hAt, hMt, by nlinarith, by nlinarith⟩

lemma optimizedCubic_eval (a x : ℝ) :
    (optimizedCubic a).eval x = x * (cubicA a - x ^ 2) / cubicScale a := by
  simp only [optimizedCubic, cubic, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

lemma cubic_lower_factor (a x : ℝ) :
    x * (cubicA a - x ^ 2) - a * (1 + a) =
      (x - a) * (1 - x) * (x + a + 1) := by
  unfold cubicA
  ring

lemma cubic_upper_factor (t x : ℝ) :
    2 * t ^ 3 - x * (3 * t ^ 2 - x ^ 2) = (x - t) ^ 2 * (x + 2 * t) := by
  ring

theorem optimized_cubic_interval (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    0 < cubicScale a ∧ 0 < improvedGap a ∧ improvedGap a < 1 ∧
    ∀ x ∈ Set.Icc a 1,
      improvedGap a ≤ (optimizedCubic a).eval x ∧
      (optimizedCubic a).eval x ≤ 1 := by
  obtain ⟨ht0, hAt, hMt, hat, ht1⟩ := criticalPoint_data ha0 ha1
  have hM : 0 < cubicScale a := by rw [hMt]; positivity
  have hφ : 0 < improvedGap a := by unfold improvedGap; positivity
  have hgap : a * (1 + a) < cubicScale a := by
    have hpos : 0 < (criticalPoint a - a) * (1 - criticalPoint a) *
        (criticalPoint a + a + 1) := by positivity
    have hf := cubic_lower_factor a (criticalPoint a)
    rw [hAt] at hf
    nlinarith [hMt]
  refine ⟨hM, hφ, (div_lt_one hM).mpr hgap, ?_⟩
  intro x hx
  have hx0 : 0 < x := ha0.trans_le hx.1
  have hlow : a * (1 + a) ≤ x * (cubicA a - x ^ 2) := by
    have hprod : 0 ≤ (x - a) * (1 - x) * (x + a + 1) := by positivity
    nlinarith [cubic_lower_factor a x]
  have hhigh : x * (cubicA a - x ^ 2) ≤ cubicScale a := by
    have hprod : 0 ≤ (x - criticalPoint a) ^ 2 * (x + 2 * criticalPoint a) := by
      positivity
    rw [hAt, hMt]
    nlinarith [cubic_upper_factor (criticalPoint a) x]
  rw [optimizedCubic_eval]
  exact ⟨div_le_div_of_nonneg_right hlow hM.le, (div_le_one hM).mpr hhigh⟩

lemma cubicScale_square {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    27 * cubicScale a ^ 2 = 4 * cubicA a ^ 3 := by
  obtain ⟨_, hA, hM, _, _⟩ := criticalPoint_data ha0 ha1
  rw [hA, hM]
  ring

lemma improvedGap_lower {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    2 * a / (1 + a ^ 2) ≤ improvedGap a := by
  have hM := (optimized_cubic_interval a ha0 ha1).1
  have hden : 0 < 1 + a ^ 2 := by positivity
  have hprod : 0 ≤ 27 * (1 + a) ^ 2 * (1 + a ^ 2) ^ 2 - 16 * cubicA a ^ 3 := by
    have heq : 27 * (1 + a) ^ 2 * (1 + a ^ 2) ^ 2 - 16 * cubicA a ^ 3 =
        (1 - a) ^ 2 * (11 * a ^ 4 + 28 * a ^ 3 + 30 * a ^ 2 + 28 * a + 11) := by
      unfold cubicA
      ring
    rw [heq]
    positivity
  have hs := cubicScale_square ha0 ha1
  have hsq : (2 * cubicScale a) ^ 2 ≤ ((1 + a) * (1 + a ^ 2)) ^ 2 := by
    nlinarith
  have hpos : 0 < (1 + a) * (1 + a ^ 2) := by positivity
  have hlinear : 2 * cubicScale a ≤ (1 + a) * (1 + a ^ 2) := by
    nlinarith
  unfold improvedGap
  apply (le_div_iff₀ hM).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  nlinarith [mul_le_mul_of_nonneg_left hlinear ha0.le]

lemma gapRatio_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < gapRatio a := by
  unfold gapRatio
  exact div_pos (sub_pos.mpr ha1) (by linarith)

lemma gapRatio_lt_one {a : ℝ} (ha0 : 0 < a) : gapRatio a < 1 := by
  unfold gapRatio
  exact (div_lt_one (by linarith)).mpr (by linarith)

lemma gapRatio_antitone {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    gapRatio b ≤ gapRatio a := by
  have hb : 0 ≤ b := ha.trans hab
  unfold gapRatio
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

lemma gapRatio_doubled (a : ℝ) (ha : 0 < a) :
    gapRatio (2 * a / (1 + a ^ 2)) = gapRatio a ^ 2 := by
  have hden : 1 + a ^ 2 ≠ 0 := by positivity
  have hplus : 1 + a ≠ 0 := by positivity
  have hsum : 1 + a ^ 2 + 2 * a ≠ 0 := by positivity
  unfold gapRatio
  field_simp [hden, hplus, hsum]
  ring

theorem optimized_cubic_ratio (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    gapRatio (improvedGap a) ≤ gapRatio a ^ 2 := by
  calc
    gapRatio (improvedGap a) ≤ gapRatio (2 * a / (1 + a ^ 2)) :=
      gapRatio_antitone (by positivity) (improvedGap_lower ha0 ha1)
    _ = gapRatio a ^ 2 := gapRatio_doubled a ha0

#assert_trust kernel optimized_cubic_interval
#print axioms optimized_cubic_interval
#assert_trust kernel optimized_cubic_ratio
#print axioms optimized_cubic_ratio

end NLA.MF02
