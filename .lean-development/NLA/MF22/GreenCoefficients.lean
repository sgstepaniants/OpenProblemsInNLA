/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Exact cancellation of the exponentially growing Green coefficient. Only
ratios of powers with ordered natural exponents are estimated; there is no
search over the dimension or approximation of a root.
-/
import NLA.MF22.ScalarTail
import Mathlib.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22

lemma norm_inverse_le_two (d : ℂ) (hd : (1 / 2 : ℝ) ≤ ‖d‖) : ‖d⁻¹‖ ≤ 2 := by
  have hp : 0 < ‖d‖ := by linarith
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ hp).mpr
  linarith

lemma norm_power_ratio_le_one (μ : ℂ) (hμ : 1 < ‖μ‖)
    (k n : ℕ) (hkn : k ≤ n) : ‖μ ^ k / μ ^ n‖ ≤ 1 := by
  have hp : 0 < ‖μ‖ ^ n := pow_pos (lt_trans zero_lt_one hμ) n
  rw [norm_div, norm_pow, norm_pow]
  apply (div_le_iff₀ hp).mpr
  simpa only [one_mul] using pow_le_pow_right₀ hμ.le hkn

lemma inverse_scaled_power_identity (γ μ d : ℂ)
    (hγ : γ ≠ 0) (hμ : μ ≠ 0) (hd : d ≠ 0) (n k : ℕ) :
    (γ * μ ^ n * d)⁻¹ * μ ^ k = γ⁻¹ * (μ ^ k / μ ^ n) * d⁻¹ := by
  field_simp [hγ, hμ, hd] <;> ring

lemma inverse_cancelled_power_identity (γ μ d : ℂ)
    (hγ : γ ≠ 0) (hμ : μ ≠ 0) (hd : d ≠ 0) (n k : ℕ) :
    (γ * μ ^ n * d)⁻¹ * γ * μ ^ k = (μ ^ k / μ ^ n) * d⁻¹ := by
  field_simp [hγ, hμ, hd] <;> ring

lemma inverse_scaled_power_bound (γ μ d : ℂ)
    (hγ : γ ≠ 0) (hμ : 1 < ‖μ‖) (hd : (1 / 2 : ℝ) ≤ ‖d‖)
    (n k : ℕ) (hkn : k ≤ n) :
    ‖(γ * μ ^ n * d)⁻¹ * μ ^ k‖ ≤ 2 / ‖γ‖ := by
  have hμ0 : μ ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hμ)
  have hd0 : d ≠ 0 := by intro he; norm_num [he] at hd
  rw [inverse_scaled_power_identity γ μ d hγ hμ0 hd0, norm_mul, norm_mul]
  calc
    ‖γ⁻¹‖ * ‖μ ^ k / μ ^ n‖ * ‖d⁻¹‖ ≤ ‖γ⁻¹‖ * 1 * 2 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (norm_power_ratio_le_one μ hμ k n hkn)
          (norm_nonneg _))
        (norm_inverse_le_two d hd) (norm_nonneg _) (by positivity)
    _ = 2 / ‖γ‖ := by rw [norm_inv]; ring

lemma inverse_cancelled_power_bound (γ μ d : ℂ)
    (hγ : γ ≠ 0) (hμ : 1 < ‖μ‖) (hd : (1 / 2 : ℝ) ≤ ‖d‖)
    (n k : ℕ) (hkn : k ≤ n) :
    ‖(γ * μ ^ n * d)⁻¹ * γ * μ ^ k‖ ≤ 2 := by
  have hμ0 : μ ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hμ)
  have hd0 : d ≠ 0 := by intro he; norm_num [he] at hd
  rw [inverse_cancelled_power_identity γ μ d hγ hμ0 hd0, norm_mul]
  calc
    ‖μ ^ k / μ ^ n‖ * ‖d⁻¹‖ ≤ 1 * 2 :=
      mul_le_mul (norm_power_ratio_le_one μ hμ k n hkn)
        (norm_inverse_le_two d hd) (norm_nonneg _) zero_le_one
    _ = 2 := by norm_num

lemma cancelled_leading_identity (γ μ d : ℂ)
    (hγ : γ ≠ 0) (hμ : μ ≠ 0) (hd : d ≠ 0)
    (n j m k : ℕ) (he : j + m = n + k) :
    μ ^ k - (γ * μ ^ n * d)⁻¹ * γ * μ ^ j * μ ^ m =
      μ ^ k * (1 - d⁻¹) := by
  have hp : μ ^ j * μ ^ m = μ ^ n * μ ^ k := by
    rw [← pow_add, ← pow_add, he]
  calc
    _ = μ ^ k - (γ * μ ^ n * d)⁻¹ * γ * (μ ^ j * μ ^ m) := by ring
    _ = μ ^ k - (γ * μ ^ n * d)⁻¹ * γ * (μ ^ n * μ ^ k) := by rw [hp]
    _ = μ ^ k * (1 - d⁻¹) := by field_simp [hγ, hμ, hd] <;> ring

lemma decayed_power_error_bound (μ d : ℂ) (hμ : 1 < ‖μ‖)
    (D : ℝ) (hD : 0 ≤ D) (n k : ℕ) (hkn : k ≤ n)
    (herr : ‖1 - d⁻¹‖ ≤ D * (‖μ‖ ^ n)⁻¹) :
    ‖μ ^ k * (1 - d⁻¹)‖ ≤ D := by
  rw [norm_mul, norm_pow]
  calc
    ‖μ‖ ^ k * ‖1 - d⁻¹‖ ≤ ‖μ‖ ^ k * (D * (‖μ‖ ^ n)⁻¹) :=
      mul_le_mul_of_nonneg_left herr (pow_nonneg (norm_nonneg _) _)
    _ = ‖μ ^ k / μ ^ n‖ * D := by
      rw [norm_div, norm_pow, norm_pow]
      ring
    _ ≤ 1 * D := mul_le_mul_of_nonneg_right
      (norm_power_ratio_le_one μ hμ k n hkn) hD
    _ = D := one_mul D

lemma green_leading_bound (γ μ d : ℂ)
    (hγ : γ ≠ 0) (hμ : 1 < ‖μ‖) (hd : (1 / 2 : ℝ) ≤ ‖d‖)
    (D : ℝ) (hD : 0 ≤ D) (n j ell : ℕ) (hj : j ≤ n) (hell : ell < n)
    (herr : ‖1 - d⁻¹‖ ≤ D * (‖μ‖ ^ n)⁻¹) :
    ‖(if ell < j then μ ^ (j - 1 - ell) else 0) -
      (γ * μ ^ n * d)⁻¹ * γ * μ ^ j * μ ^ (n - 1 - ell)‖ ≤ D + 2 := by
  have hμ0 : μ ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hμ)
  have hd0 : d ≠ 0 := by intro he; norm_num [he] at hd
  by_cases hlt : ell < j
  · rw [if_pos hlt, cancelled_leading_identity γ μ d hγ hμ0 hd0
      n j (n - 1 - ell) (j - 1 - ell) (by omega)]
    have he := decayed_power_error_bound μ d hμ D hD n (j - 1 - ell)
      (by omega) herr
    linarith
  · rw [if_neg hlt, zero_sub, norm_neg]
    have he : (γ * μ ^ n * d)⁻¹ * γ * μ ^ j * μ ^ (n - 1 - ell) =
        (γ * μ ^ n * d)⁻¹ * γ * μ ^ (j + (n - 1 - ell)) := by
      rw [pow_add]
      ring
    rw [he]
    have hb := inverse_cancelled_power_bound γ μ d hγ hμ hd n
      (j + (n - 1 - ell)) (by omega)
    linarith

#assert_trust kernel green_leading_bound
#print axioms green_leading_bound

end NLA.MF22
