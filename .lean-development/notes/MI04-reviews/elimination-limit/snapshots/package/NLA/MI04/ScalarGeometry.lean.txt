/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Exact scalar square bounds and affine reconstruction, including coincident values.
-/
import NLA.MI04.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexConjugate

namespace NLA.MI04

/-- The exact one-coordinate inequality consumed by the all-vector upper bound. -/
lemma weighted_square_bound (q : ℝ) (hq : 0 < q) (z w : ℂ) :
    2 * (z * star w).re - q * Complex.normSq w ≤ Complex.normSq z / q := by
  apply (le_div_iff₀ hq).mpr
  have h := Complex.normSq_nonneg (z - (q : ℂ) * w)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, zero_add] at h
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  nlinarith

lemma real_ratio_of_zero_orientation (a b : ℂ)
    (h : (a * star b).im = 0) : (a / b).im = 0 := by
  rw [Complex.div_im, ← sub_div]
  have hnum : a.im * b.re - a.re * b.im = 0 := by
    simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im] at h
    nlinarith only [h]
  rw [hnum, zero_div]

theorem collinear_values_affine {n : ℕ} (hn : 1 ≤ n) (z : Fin n → ℂ)
    (hz : ∀ i j k : Fin n, ((z i - z k) * star (z j - z k)).im = 0) :
    ∃ α β : ℂ, ∃ t : Fin n → ℝ, ∀ j, z j = α * (t j : ℂ) + β := by
  classical
  let a : Fin n := ⟨0, by omega⟩
  by_cases hall : ∀ j, z j = z a
  · exact ⟨0, z a, fun _ => 0, fun j => by simpa using hall j⟩
  push_neg at hall
  obtain ⟨b, hb⟩ := hall
  let α : ℂ := z b - z a
  have hα : α ≠ 0 := sub_ne_zero.mpr hb
  refine ⟨α, z a, fun j => ((z j - z a) / α).re, ?_⟩
  intro j
  have him : ((z j - z a) / α).im = 0 :=
    real_ratio_of_zero_orientation (z j - z a) α (hz j b a)
  have hre : ((((z j - z a) / α).re : ℝ) : ℂ) = (z j - z a) / α := by
    apply Complex.ext
    · rfl
    · simpa using him.symm
  rw [hre]
  field_simp [hα] <;> ring

#print axioms weighted_square_bound
#assert_trust kernel weighted_square_bound
#print axioms collinear_values_affine
#assert_trust kernel collinear_values_affine

end NLA.MI04
