/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The complete unconditional four-root classification, including rho^2=10.
The source family and earlier root classification retain the credit stated
in the frozen definitions and source-correspondence document.
-/
import NLA.MF22.RootCayley
import NLA.MF22.RootCubic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open Polynomial

theorem four_roots (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ roots : Fin 4 → ℂ, RootData ρ roots := by
  by_cases hρ2 : ρ ^ 2 = 10
  · have he := exceptional_parameter ρ hρ hρ2
    have ha : 25 * ρ ≠ 0 := by positivity
    have hd : (20 : ℝ) ^ 2 - 4 * (25 * ρ) * (15 * ρ) < 0 := by
      rw [he.2.1]
      norm_num
    obtain ⟨z, hz, hqz, hqs⟩ := negative_quadratic_pair (25 * ρ) 20 (15 * ρ) ha hd
    have hpoly (x : ℂ) : (complexCubic ρ).eval x =
        ((25 * ρ : ℝ) : ℂ) * x ^ 2 + (20 : ℂ) * x + ((15 * ρ : ℝ) : ℂ) := by
      simp [complexCubic, he.1]
    have hcz : (complexCubic ρ).eval z = 0 := by rw [hpoly]; exact hqz
    have hcs : (complexCubic ρ).eval (star z) = 0 := by rw [hpoly]; exact hqs
    apply rootData_of_quotient_configuration ρ hρ (-1) (cayley z) (cayley (star z))
    · simp
    · exact cayley_upper_norm z hz
    · exact cayley_lower_norm (star z) (by simpa using neg_neg_of_pos hz)
        (cubic_root_not_pole ρ hρ (star z) hcs)
    · exact he.2.2.1
    · exact cayley_quotient_root ρ hρ z hcz
    · exact cayley_quotient_root ρ hρ (star z) hcs
  · have ha : (realCubic ρ).a ≠ 0 := by
      change 6 * (ρ ^ 2 - 10) ≠ 0
      exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hρ2)
    obtain ⟨r, z, hz, hcr, hcz, hcs⟩ := negative_cubic_configuration (realCubic ρ) ha
      (real_cubic_discriminant ρ hρ).2.1
    change (complexCubic ρ).eval (r : ℂ) = 0 at hcr
    change (complexCubic ρ).eval z = 0 at hcz
    change (complexCubic ρ).eval (star z) = 0 at hcs
    apply rootData_of_quotient_configuration ρ hρ (cayley (r : ℂ))
      (cayley z) (cayley (star z))
    · exact cayley_real_norm r
    · exact cayley_upper_norm z hz
    · exact cayley_lower_norm (star z) (by simpa using neg_neg_of_pos hz)
        (cubic_root_not_pole ρ hρ (star z) hcs)
    · exact cayley_quotient_root ρ hρ (r : ℂ) hcr
    · exact cayley_quotient_root ρ hρ z hcz
    · exact cayley_quotient_root ρ hρ (star z) hcs

#assert_trust kernel four_roots
#print axioms four_roots

end NLA.MF22
