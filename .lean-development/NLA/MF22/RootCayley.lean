/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Exact Cayley geometry and the source-polynomial bridge. No interval isolation
or numerical approximation to a root is used.
-/
import NLA.MF22.ScalarCertificates

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open Polynomial

lemma cayley_denominator_ne_zero (x : ℂ) (hx : x ≠ -Complex.I) :
    1 - Complex.I * x ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp [Complex.mul_re, Complex.mul_im] at hr hi
  apply hx
  apply Complex.ext
  · simp only [Complex.neg_re, Complex.I_re]
    linarith
  · simp only [Complex.neg_im, Complex.I_im]
    linarith

lemma cayley_denominator_normSq (x : ℂ) :
    Complex.normSq (1 - Complex.I * x) = (1 + x.im) ^ 2 + x.re ^ 2 := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

lemma cayley_numerator_normSq (x : ℂ) :
    Complex.normSq (1 + Complex.I * x) = (1 - x.im) ^ 2 + x.re ^ 2 := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im] <;> ring

lemma cayley_normSq (x : ℂ) :
    Complex.normSq (cayley x) =
      ((1 - x.im) ^ 2 + x.re ^ 2) / ((1 + x.im) ^ 2 + x.re ^ 2) := by
  rw [cayley, Complex.normSq_div, cayley_numerator_normSq,
    cayley_denominator_normSq]

lemma cayley_real_norm (x : ℝ) : ‖cayley (x : ℂ)‖ = 1 := by
  have hd : (1 : ℝ) + x ^ 2 ≠ 0 := by positivity
  have hs : Complex.normSq (cayley (x : ℂ)) = 1 := by
    rw [cayley_normSq]
    simp [hd]
  rw [Complex.normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (cayley (x : ℂ))]

lemma cayley_upper_norm (x : ℂ) (hx : 0 < x.im) : ‖cayley x‖ < 1 := by
  have hd : 0 < (1 + x.im) ^ 2 + x.re ^ 2 := by
    nlinarith [sq_nonneg x.re, sq_nonneg x.im]
  have hs : Complex.normSq (cayley x) < 1 := by
    rw [cayley_normSq]
    apply (div_lt_one hd).mpr
    nlinarith
  rw [Complex.normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (cayley x)]

lemma cayley_lower_norm (x : ℂ) (hx : x.im < 0) (hp : x ≠ -Complex.I) :
    1 < ‖cayley x‖ := by
  have hd : 0 < (1 + x.im) ^ 2 + x.re ^ 2 := by
    rw [← cayley_denominator_normSq]
    exact Complex.normSq_pos.mpr (cayley_denominator_ne_zero x hp)
  apply Complex.one_lt_normSq_iff.mp
  rw [cayley_normSq]
  apply (one_lt_div hd).mpr
  nlinarith

lemma cubic_root_not_pole (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ)
    (hx : (complexCubic ρ).eval x = 0) : x ≠ -Complex.I := by
  intro he
  rw [he] at hx
  exact (real_cubic_discriminant ρ hρ).2.2.2 hx

lemma cayley_quotient_root (ρ : ℝ) (hρ : 0 < ρ) (x : ℂ)
    (hx : (complexCubic ρ).eval x = 0) :
    (quotientCubic ρ).eval (cayley x) = 0 := by
  have hp := cayley_denominator_ne_zero x (cubic_root_not_pole ρ hρ x hx)
  have he := cayley_identity ρ x hp
  rw [hx, mul_zero] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero 3 hp)

lemma quotient_root_is_quartic_root (ρ : ℝ) (z : ℂ)
    (hz : (quotientCubic ρ).eval z = 0) : (quartic ρ).IsRoot z := by
  rw [Polynomial.IsRoot, (quartic_factorization ρ).1]
  simp [hz]

lemma quartic_root_ne_zero (ρ : ℝ) (hρ : 0 < ρ) (z : ℂ)
    (hz : (quartic ρ).IsRoot z) : z ≠ 0 := by
  intro he
  rw [he] at hz
  have hs : star (leadingScalar ρ) = 0 := by simpa [Polynomial.IsRoot, quartic] using hz
  apply leading_scalar_ne_zero ρ hρ
  simpa using congrArg star hs

lemma quotient_one_ne_zero (ρ : ℝ) (hρ : 0 < ρ) :
    (quotientCubic ρ).eval 1 ≠ 0 := by
  rw [(quartic_factorization ρ).2.1]
  exact mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hρ.ne')

/-- Pairwise-distinct norm classes, with the second unit root separated from
one by the literal quotient evaluation, assemble the frozen root datum. -/
lemma rootData_of_quotient_configuration (ρ : ℝ) (hρ : 0 < ρ)
    (t u v : ℂ) (ht : ‖t‖ = 1) (hu : ‖u‖ < 1) (hv : 1 < ‖v‖)
    (hqt : (quotientCubic ρ).eval t = 0)
    (hqu : (quotientCubic ρ).eval u = 0)
    (hqv : (quotientCubic ρ).eval v = 0) :
    ∃ roots : Fin 4 → ℂ, RootData ρ roots := by
  have h1t : (1 : ℂ) ≠ t := by
    intro he
    rw [← he] at hqt
    exact quotient_one_ne_zero ρ hρ hqt
  have h1u : (1 : ℂ) ≠ u := by intro he; simpa [← he] using hu
  have h1v : (1 : ℂ) ≠ v := by intro he; simpa [← he] using hv
  have htu : t ≠ u := by
    intro he
    rw [← he, ht] at hu
    exact (lt_irrefl _ hu)
  have htv : t ≠ v := by
    intro he
    rw [← he, ht] at hv
    exact (lt_irrefl _ hv)
  have huv : u ≠ v := by
    intro he
    rw [he] at hu
    exact (not_lt_of_ge hv.le hu)
  have hroot (z : ℂ) (hz : (quotientCubic ρ).eval z = 0) :
      z ≠ 0 ∧ (quartic ρ).IsRoot z :=
    ⟨quartic_root_ne_zero ρ hρ z (quotient_root_is_quartic_root ρ z hz),
      quotient_root_is_quartic_root ρ z hz⟩
  let roots : Fin 4 → ℂ := ![1, t, u, v]
  refine ⟨roots, ?_, ?_, rfl, ht, hu, hv⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [roots, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.vecHead, Matrix.vecTail]
  · intro i
    fin_cases i
    · refine ⟨one_ne_zero, ?_⟩
      rw [Polynomial.IsRoot, (quartic_factorization ρ).1]
      simp [roots]
    · exact hroot t hqt
    · exact hroot u hqu
    · exact hroot v hqv

#assert_trust kernel rootData_of_quotient_configuration
#print axioms rootData_of_quotient_configuration

end NLA.MF22
