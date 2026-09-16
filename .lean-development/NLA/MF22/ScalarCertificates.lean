/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Exact identities in one real parameter. A single scalar LeanCert certificate
and completion of the square avoid all interval subdivisions of the parameter.
-/
import NLA.MF22.Definitions
import Mathlib.Tactic
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open Polynomial

lemma discriminant_gap_certificate : (0 : ℝ) < 5280431 := by
  interval_decide (trust := kernel)

lemma leading_scalar_ne_zero (ρ : ℝ) (hρ : 0 < ρ) : leadingScalar ρ ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp [leadingScalar, ← Complex.ofReal_pow] at hi
  linarith

lemma conjugate_leadingScalar (ρ : ℝ) :
    star (leadingScalar ρ) = 30 - (ρ : ℂ) ^ 2 + 10 * Complex.I * (ρ : ℂ) := by
  simp [leadingScalar]

lemma conjugate_middleScalar (ρ : ℝ) :
    star (middleScalar ρ) = 24 * (ρ : ℂ) ^ 2 - 80 * Complex.I * (ρ : ℂ) - 240 := by
  simp [middleScalar]
  ring

lemma complexCubic_eval (ρ : ℝ) (x : ℂ) :
    (complexCubic ρ).eval x =
      6 * ((ρ : ℂ) ^ 2 - 10) * x ^ 3 + 25 * (ρ : ℂ) * x ^ 2 +
        5 * ((ρ : ℂ) ^ 2 - 6) * x + 15 * (ρ : ℂ) := by
  simp [complexCubic, realCubic, Cubic.toPoly]

theorem quartic_factorization (ρ : ℝ) :
    quartic ρ = (X - 1) * quotientCubic ρ ∧
    (quotientCubic ρ).eval 1 = 120 * Complex.I * (ρ : ℂ) ∧
    (quotientCubic ρ).eval (-1) = 48 * ((ρ : ℂ) ^ 2 - 10) := by
  constructor
  · simp only [quartic, quotientCubic]
    simp only [conjugate_leadingScalar, conjugate_middleScalar]
    simp only [leadingScalar, middleScalar, centralScalar,
      map_add, map_sub, map_mul, map_pow, map_ofNat]
    ring
  · constructor
    all_goals
      simp only [quotientCubic, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]
      simp only [conjugate_leadingScalar, conjugate_middleScalar]
      simp only [leadingScalar, middleScalar]
      ring

theorem cayley_identity (ρ : ℝ) (x : ℂ) (hx : 1 - Complex.I * x ≠ 0) :
    (1 - Complex.I * x) ^ 3 * (quotientCubic ρ).eval (cayley x) =
      8 * Complex.I * (complexCubic ρ).eval x := by
  rw [complexCubic_eval]
  simp only [quotientCubic, eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  simp only [conjugate_leadingScalar, conjugate_middleScalar]
  simp only [leadingScalar, middleScalar, cayley]
  field_simp [hx] <;>
    ring_nf <;> simp only [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four] <;> ring

theorem positive_discriminant_factor (y : ℝ) :
    0 < 120 * y ^ 2 - 3337 * y + 34200 := by
  have he : 480 * (120 * y ^ 2 - 3337 * y + 34200) =
      (240 * y - 3337) ^ 2 + 5280431 := by ring
  have hg := discriminant_gap_certificate
  nlinarith [sq_nonneg (240 * y - 3337)]

theorem real_cubic_discriminant (ρ : ℝ) (hρ : 0 < ρ) :
    (realCubic ρ).discr =
      -25 * ρ ^ 4 * (120 * ρ ^ 4 - 3337 * ρ ^ 2 + 34200) -
        5269500 * ρ ^ 2 - 6480000 ∧
    (realCubic ρ).discr < 0 ∧
    (complexCubic ρ).eval (-Complex.I) = -Complex.I * leadingScalar ρ ∧
    (complexCubic ρ).eval (-Complex.I) ≠ 0 := by
  have hd : (realCubic ρ).discr =
      -25 * ρ ^ 4 * (120 * ρ ^ 4 - 3337 * ρ ^ 2 + 34200) -
        5269500 * ρ ^ 2 - 6480000 := by
    dsimp [realCubic, Cubic.discr]
    ring
  have hp : 0 < 120 * ρ ^ 4 - 3337 * ρ ^ 2 + 34200 := by
    convert positive_discriminant_factor (ρ ^ 2) using 1 <;> ring
  have he : (complexCubic ρ).eval (-Complex.I) = -Complex.I * leadingScalar ρ := by
    rw [complexCubic_eval]
    unfold leadingScalar
    ring_nf <;> simp only [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four] <;> ring
  refine ⟨hd, ?_, he, ?_⟩
  · rw [hd]
    have hprod : 0 ≤ 25 * ρ ^ 4 * (120 * ρ ^ 4 - 3337 * ρ ^ 2 + 34200) :=
      mul_nonneg (mul_nonneg (by norm_num) (by positivity)) hp.le
    nlinarith [sq_nonneg ρ]
  · rw [he]
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (leading_scalar_ne_zero ρ hρ)

theorem exceptional_parameter (ρ : ℝ) (hρ : 0 < ρ) (hρ2 : ρ ^ 2 = 10) :
    (realCubic ρ).toPoly = C (25 * ρ) * X ^ 2 + C 20 * X + C (15 * ρ) ∧
    (20 : ℝ) ^ 2 - 4 * (25 * ρ) * (15 * ρ) = -14600 ∧
    (quotientCubic ρ).eval (-1) = 0 ∧
    (quotientCubic ρ).derivative.eval (-1) = -100 * Complex.I * (ρ : ℂ) ∧
    (quotientCubic ρ).derivative.eval (-1) ≠ 0 := by
  have hc : (ρ : ℂ) ^ 2 = 10 := by exact_mod_cast hρ2
  have he : (quotientCubic ρ).derivative.eval (-1) =
      -100 * Complex.I * (ρ : ℂ) := by
    simp [quotientCubic, leadingScalar, middleScalar, hc] <;> ring
  refine ⟨?_, ?_, ?_, he, ?_⟩
  · norm_num [realCubic, Cubic.toPoly, hρ2, map_ofNat] <;> ring
  · nlinarith [hρ2]
  · rw [(quartic_factorization ρ).2.2, hc]
    ring
  · rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hρ.ne')

#assert_trust kernel quartic_factorization
#print axioms quartic_factorization
#assert_trust kernel cayley_identity
#print axioms cayley_identity
#assert_trust kernel positive_discriminant_factor
#print axioms positive_discriminant_factor
#assert_trust kernel real_cubic_discriminant
#print axioms real_cubic_discriminant
#assert_trust kernel exceptional_parameter
#print axioms exceptional_parameter

end NLA.MF22
