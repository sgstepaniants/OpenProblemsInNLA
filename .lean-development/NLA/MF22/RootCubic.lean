/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Generic real cubic classification via one real root and an exact quadratic
discriminant identity. Complex root existence reuses Mathlib's theorem; no
numerical approximation, root-isolation computation or parameter subdivision.
-/
import NLA.MF22.Definitions
import Mathlib.Analysis.Polynomial.Order
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open Polynomial

lemma real_cubic_has_root (P : Cubic ℝ) (ha : P.a ≠ 0) :
    ∃ r : ℝ, P.toPoly.IsRoot r := by
  by_contra! h
  have hl : ∀ y, P.toPoly.IsRoot y → y < (0 : ℝ) := fun y hy => (h y hy).elim
  have hr : ∀ y, P.toPoly.IsRoot y → (0 : ℝ) < y := fun y hy => (h y hy).elim
  have hd : P.toPoly.natDegree = 3 := Cubic.natDegree_of_a_ne_zero ha
  rcases le_total 0 P.toPoly.leadingCoeff with hc | hc
  · have hpos := Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hl hc
    have hneg := Polynomial.zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg hr hc
    norm_num [hd] at hneg
    linarith
  · have hneg := Polynomial.eval_lt_zero_of_roots_lt_of_leadingCoeff_nonpos hl hc
    have hpos := Polynomial.negOnePow_mul_eval_lt_zero_of_lt_roots_of_leadingCoeff_nonpos hr hc
    norm_num [hd] at hpos
    linarith

/-- A negative-discriminant real quadratic has a root in the upper half-plane
and its conjugate root. Only qualitative existence from Mathlib is required. -/
lemma negative_quadratic_pair (a b c : ℝ) (ha : a ≠ 0)
    (hd : b ^ 2 - 4 * a * c < 0) :
    ∃ z : ℂ, 0 < z.im ∧
      ((a : ℂ) * z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0) ∧
      ((a : ℂ) * (star z) ^ 2 + (b : ℂ) * star z + (c : ℂ) = 0) := by
  let Q : ℂ[X] := C (a : ℂ) * X ^ 2 + C (b : ℂ) * X + C (c : ℂ)
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  have hdeg : Q.degree = 2 := by dsimp [Q]; exact degree_quadratic hac
  obtain ⟨z, hz⟩ := Complex.exists_root (f := Q) (by rw [hdeg]; norm_num)
  have he : (a : ℂ) * z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0 := by
    simpa [Polynomial.IsRoot, Q] using hz
  have hs : (a : ℂ) * (star z) ^ 2 + (b : ℂ) * star z + (c : ℂ) = 0 := by
    simpa using congrArg star he
  have him : z.im ≠ 0 := by
    intro hi
    have hzre : z = (z.re : ℂ) := by
      apply Complex.ext <;> simp [hi]
    have hreal : a * (z.re * z.re) + b * z.re + c = 0 := by
      have hh := he
      rw [hzre] at hh
      have hp : a * z.re ^ 2 + b * z.re + c = 0 := by exact_mod_cast hh
      simpa only [pow_two] using hp
    have hdq := discrim_eq_sq_of_quadratic_eq_zero hreal
    unfold discrim at hdq
    nlinarith [sq_nonneg (2 * a * z.re + b)]
  rcases lt_or_gt_of_ne him with hi | hi
  · refine ⟨star z, ?_, hs, ?_⟩
    · simpa using neg_pos.mpr hi
    · simpa using he
  · exact ⟨z, hi, he, hs⟩

/-- The literal cubic with negative discriminant supplies one real root and
a conjugate pair with strictly positive/negative imaginary parts. -/
lemma negative_cubic_configuration (P : Cubic ℝ) (ha : P.a ≠ 0)
    (hdisc : P.discr < 0) :
    ∃ r : ℝ, ∃ z : ℂ, 0 < z.im ∧
      (P.toPoly.map Complex.ofRealHom).eval (r : ℂ) = 0 ∧
      (P.toPoly.map Complex.ofRealHom).eval z = 0 ∧
      (P.toPoly.map Complex.ofRealHom).eval (star z) = 0 := by
  obtain ⟨r, hr⟩ := real_cubic_has_root P ha
  have he : P.a * r ^ 3 + P.b * r ^ 2 + P.c * r + P.d = 0 := by
    simpa [Polynomial.IsRoot, Cubic.toPoly] using hr
  let b := P.b + P.a * r
  let c := P.c + b * r
  have hd : P.discr = (b ^ 2 - 4 * P.a * c) * (3 * P.a * r ^ 2 + 2 * P.b * r + P.c) ^ 2 := by
    have hpd : P.d = -(P.a * r ^ 3 + P.b * r ^ 2 + P.c * r) := by linarith
    simp only [Cubic.discr, hpd]
    dsimp [b, c]
    ring
  have hq : b ^ 2 - 4 * P.a * c < 0 := by
    by_contra! hq
    have hp := mul_nonneg hq (sq_nonneg (3 * P.a * r ^ 2 + 2 * P.b * r + P.c))
    rw [← hd] at hp
    exact (not_lt_of_ge hp hdisc)
  obtain ⟨z, hz, hqz, hqs⟩ := negative_quadratic_pair P.a b c ha hq
  have hdcomplex : (P.d : ℂ) = -((P.a : ℂ) * (r : ℂ) ^ 3 +
      (P.b : ℂ) * (r : ℂ) ^ 2 + (P.c : ℂ) * (r : ℂ)) := by
    exact_mod_cast (show P.d = -(P.a * r ^ 3 + P.b * r ^ 2 + P.c * r) by linarith)
  have hfactor (x : ℂ) : (P.toPoly.map Complex.ofRealHom).eval x =
      (x - (r : ℂ)) * ((P.a : ℂ) * x ^ 2 + (b : ℂ) * x + (c : ℂ)) := by
    simp [Cubic.toPoly, b, c, hdcomplex] <;> ring
  refine ⟨r, z, hz, ?_, ?_, ?_⟩
  · rw [hfactor]
    simp
  · rw [hfactor, hqz, mul_zero]
  · rw [hfactor, hqs, mul_zero]

#assert_trust kernel negative_cubic_configuration
#print axioms negative_cubic_configuration

end NLA.MF22
