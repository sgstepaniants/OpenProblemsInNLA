/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Exact scalar certificates exclude cancellation in the source generating
function. The proof uses a quadratic elimination identity, without computing
an abstract resultant or subdividing the unbounded parameter interval.
-/
import NLA.MF22.ScalarCertificates
import Mathlib.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open Polynomial

noncomputable section

def auxiliaryAlpha (ρ : ℝ) (z : ℂ) : ℂ :=
  coefficientA ρ - 24 * (ρ : ℂ) * z + coefficientF ρ * z ^ 2

def auxiliaryH (ρ : ℝ) (z : ℂ) : ℂ :=
  coefficientB ρ + 96 * Complex.I * z + coefficientC ρ * z ^ 2

def auxiliaryEll (ρ : ℝ) (z : ℂ) : ℂ :=
  coefficientD ρ + 24 * (ρ : ℂ) * z + coefficientE ρ * z ^ 2

lemma generating_identities (ρ : ℝ) (z : ℂ) :
    coefficientA ρ * auxiliaryEll ρ z - coefficientB ρ * auxiliaryH ρ z =
      24 * (numerator ρ).eval z ∧
    auxiliaryAlpha ρ z * auxiliaryEll ρ z - (auxiliaryH ρ z) ^ 2 =
      24 * (denominator ρ).eval z := by
  constructor <;>
    simp only [auxiliaryAlpha, auxiliaryH, auxiliaryEll, numerator, denominator,
      eval_add, eval_mul, eval_pow, eval_C, eval_X] <;>
    try simp only [conjugate_leadingScalar, conjugate_middleScalar]
  all_goals
    simp only [coefficientA, coefficientB, coefficientC,
      coefficientD, coefficientE, coefficientF, leadingScalar, middleScalar,
      centralScalar] <;>
    ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four] <;> ring

lemma quadratic_common_root_identity (a b c d e f z : ℂ)
    (hp : a * z ^ 2 + b * z + c = 0)
    (hq : d * z ^ 2 + e * z + f = 0) :
    (a * f - c * d) ^ 2 - (a * e - b * d) * (b * f - c * e) = 0 := by
  have hfirst : (a * e - b * d) * z + (a * f - c * d) = 0 := by
    linear_combination a * hq - d * hp
  have hsecond : (b * f - c * e) - (a * e - b * d) * z ^ 2 = 0 := by
    linear_combination b * hq - e * hp
  linear_combination
    ((a * f - c * d) - (a * e - b * d) * z) * hfirst -
      (a * e - b * d) * hsecond

lemma auxiliary_no_common_root (ρ : ℝ) (z : ℂ)
    (hh : auxiliaryH ρ z = 0) : auxiliaryEll ρ z ≠ 0 := by
  intro he
  have hp : coefficientC ρ * z ^ 2 + (96 * Complex.I) * z + coefficientB ρ = 0 := by
    simpa only [auxiliaryH, add_comm, add_left_comm, add_assoc] using hh
  have hq : coefficientE ρ * z ^ 2 + (24 * (ρ : ℂ)) * z + coefficientD ρ = 0 := by
    simpa only [auxiliaryEll, add_comm, add_left_comm, add_assoc] using he
  have hr := quadratic_common_root_identity (coefficientC ρ) (96 * Complex.I)
    (coefficientB ρ) (coefficientE ρ) (24 * (ρ : ℂ)) (coefficientD ρ) z hp hq
  have hid :
      (coefficientC ρ * coefficientD ρ - coefficientB ρ * coefficientE ρ) ^ 2 -
        (coefficientC ρ * (24 * (ρ : ℂ)) - (96 * Complex.I) * coefficientE ρ) *
          ((96 * Complex.I) * coefficientD ρ - coefficientB ρ * (24 * (ρ : ℂ))) =
      2177280 + 946944 * (ρ : ℂ) ^ 2 +
        Complex.I * (622080 * (ρ : ℂ) + 241920 * (ρ : ℂ) ^ 3) := by
    unfold coefficientB coefficientC coefficientD coefficientE
    ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four] <;> ring
  rw [hid] at hr
  have hre := congrArg Complex.re hr
  norm_num [Complex.mul_re, ← Complex.ofReal_pow] at hre
  nlinarith [sq_nonneg ρ]

lemma coefficientA_ne_zero (ρ : ℝ) : coefficientA ρ ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num [coefficientA] at hi

lemma root_denominator_ne_zero (ρ : ℝ) :
    7 * (ρ : ℂ) ^ 2 + 30 + 22 * Complex.I * (ρ : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [Complex.mul_re, ← Complex.ofReal_pow] at hre
  nlinarith [sq_nonneg ρ]

lemma auxiliary_elimination (ρ : ℝ) (z : ℂ) :
    coefficientA ρ * auxiliaryH ρ z - coefficientB ρ * auxiliaryAlpha ρ z =
      24 * z * (24 - 7 * (ρ : ℂ) ^ 2 - 34 * Complex.I * (ρ : ℂ) +
        (7 * (ρ : ℂ) ^ 2 + 30 + 22 * Complex.I * (ρ : ℂ)) * z) := by
  unfold auxiliaryH auxiliaryAlpha coefficientA coefficientB coefficientC coefficientF
  ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four] <;> ring

lemma clear_quadratic_denominator (a b c u d : ℂ) (hd : d ≠ 0) :
    d ^ 2 * (a + b * (u / d) + c * (u / d) ^ 2) =
      a * d ^ 2 + b * u * d + c * u ^ 2 := by
  field_simp [hd] <;> ring

lemma substituted_numerator (ρ : ℝ) :
    let d : ℂ := 7 * (ρ : ℂ) ^ 2 + 30 + 22 * Complex.I * (ρ : ℂ)
    let u : ℂ := 7 * (ρ : ℂ) ^ 2 - 24 + 34 * Complex.I * (ρ : ℂ)
    d ^ 2 * (numerator ρ).eval (u / d) =
      (134136 + 32436 * (ρ : ℂ) ^ 2 - 10404 * (ρ : ℂ) ^ 4) +
        Complex.I * (ρ : ℂ) *
          (-103032 - 40632 * (ρ : ℂ) ^ 2 + 840 * (ρ : ℂ) ^ 4) := by
  dsimp
  simp only [numerator, eval_add, eval_mul, eval_pow, eval_C, eval_X]
  rw [clear_quadratic_denominator _ _ _ _ _ (root_denominator_ne_zero ρ)]
  unfold leadingScalar
  ring_nf <;> norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four] <;> ring

theorem numerator_denominator_coprime (ρ : ℝ) (hρ : 0 < ρ) (z : ℂ)
    (hN : (numerator ρ).eval z = 0) : (denominator ρ).eval z ≠ 0 := by
  intro hd
  have hz : z ≠ 0 := by
    intro he
    subst z
    have ha : leadingScalar ρ = 0 := by simpa [numerator] using hN
    exact leading_scalar_ne_zero ρ hρ ha
  have heq₁ : coefficientA ρ * auxiliaryEll ρ z = coefficientB ρ * auxiliaryH ρ z := by
    have h := (generating_identities ρ z).1
    rw [hN, mul_zero] at h
    exact sub_eq_zero.mp h
  have heq₂ : auxiliaryAlpha ρ z * auxiliaryEll ρ z = (auxiliaryH ρ z) ^ 2 := by
    have h := (generating_identities ρ z).2
    rw [hd, mul_zero] at h
    exact sub_eq_zero.mp h
  have hh : auxiliaryH ρ z ≠ 0 := by
    intro he
    have hl : auxiliaryEll ρ z = 0 := by
      rw [he, mul_zero] at heq₁
      exact (mul_eq_zero.mp heq₁).resolve_left (coefficientA_ne_zero ρ)
    exact auxiliary_no_common_root ρ z he hl
  have hex : coefficientA ρ * auxiliaryH ρ z = coefficientB ρ * auxiliaryAlpha ρ z := by
    apply mul_right_cancel₀ hh
    calc
      _ = coefficientA ρ * (auxiliaryH ρ z) ^ 2 := by ring
      _ = coefficientA ρ * (auxiliaryAlpha ρ z * auxiliaryEll ρ z) := by rw [heq₂]
      _ = coefficientB ρ * auxiliaryAlpha ρ z * auxiliaryH ρ z := by
        linear_combination auxiliaryAlpha ρ z * heq₁
  have hzero : 24 - 7 * (ρ : ℂ) ^ 2 - 34 * Complex.I * (ρ : ℂ) +
      (7 * (ρ : ℂ) ^ 2 + 30 + 22 * Complex.I * (ρ : ℂ)) * z = 0 := by
    have h := auxiliary_elimination ρ z
    rw [hex, sub_self] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (mul_ne_zero (by norm_num) hz)
  have hzexact : z = (7 * (ρ : ℂ) ^ 2 - 24 + 34 * Complex.I * (ρ : ℂ)) /
      (7 * (ρ : ℂ) ^ 2 + 30 + 22 * Complex.I * (ρ : ℂ)) := by
    apply (eq_div_iff (root_denominator_ne_zero ρ)).mpr
    linear_combination hzero
  rw [hzexact] at hN
  have he := substituted_numerator ρ
  dsimp at he
  rw [hN, mul_zero] at he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  norm_num [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow] at hre him
  have hi : -103032 - 40632 * ρ ^ 2 + 840 * ρ ^ 4 = 0 :=
    him.resolve_left hρ.ne'
  have hcombine :
      70 * (134136 + 32436 * ρ ^ 2 - 10404 * ρ ^ 4) +
        867 * (-103032 - 40632 * ρ ^ 2 + 840 * ρ ^ 4) =
      -79939224 - 32957424 * ρ ^ 2 := by ring
  nlinarith [sq_nonneg ρ]

#assert_trust kernel numerator_denominator_coprime
#print axioms numerator_denominator_coprime

end
end NLA.MF22
