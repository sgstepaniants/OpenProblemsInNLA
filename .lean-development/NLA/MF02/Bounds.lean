/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Bounds on the actual coefficient infima, including both small budgets.
-/
import NLA.MF02.Chebyshev
import NLA.MF02.Iteration
import Mathlib.Order.Monotone.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF02
open Polynomial

lemma oddPart_uniformError_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (p : ℝ[X]) : uniformError δ (oddPart p) ≤ uniformError δ p :=
  uniformError_odd_bound hδ0 hδ1 (oddPart p) (oddPart_odd p)
    (fun _ hx => oddPart_error_le hδ0 hδ1 p hx)

/-- Even coefficients cancel under symmetrization. In particular, the odd
part of every quadratic is linear; the original polynomial need not be odd. -/
lemma oddPart_degree_le_one {p : ℝ[X]} (hp : p.natDegree ≤ 2) :
    (oddPart p).natDegree ≤ 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases htwo : n = 2
  · subst n
    have heq := congrArg (fun q : ℝ[X] => q.coeff 2) (oddPart_comp_neg p)
    have hX : (-X : ℝ[X]) = C (-1) * X := by simp
    rw [hX, comp_C_mul_X_coeff, coeff_neg] at heq
    norm_num at heq
    linarith
  · apply coeff_eq_zero_of_natDegree_lt
    have hdeg := (oddPart_degree_le p).trans hp
    omega

lemma unrestrictedError_upper_linear (m : ℕ) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) : unrestrictedError m δ ≤ gapRatio δ := by
  have hp : ProgramComputable m (C (2 / (1 + δ)) * X) := by
    simpa using programComputable_linear m 0 (2 / (1 + δ))
  exact (unrestrictedError_le hδ0 hδ1 hp).trans
    (centered_polynomial_error hδ0 hδ1 hδ0 X (by intro x; simp)
      (by intro x hx; simpa only [eval_X] using hx))

lemma unrestrictedError_eq_gapRatio_of_le_one (m : ℕ) (hm : m ≤ 1)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    unrestrictedError m δ = gapRatio δ := by
  apply le_antisymm (unrestrictedError_upper_linear m δ hδ0 hδ1)
  apply le_unrestrictedError
  intro p hp
  have hdeg : p.natDegree ≤ 2 := by
    have hg := (program_degree_bound m p hp).trans
      (Nat.pow_le_pow_right (by decide : 0 < 2) hm)
    simpa using hg
  have hlower := degree_error_lower_bound δ hδ0 hδ1 1 (by decide)
    (oddPart p) (oddPart_degree_le_one hdeg)
  have hlower' : gapRatio δ ≤ uniformError δ (oddPart p) := by simpa using hlower
  exact hlower'.trans (oddPart_uniformError_le hδ0 hδ1 p)

theorem unrestricted_error_small_budgets (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    unrestrictedError 0 δ = gapRatio δ ∧
    unrestrictedError 1 δ = gapRatio δ :=
  ⟨unrestrictedError_eq_gapRatio_of_le_one 0 (by decide) δ hδ0 hδ1,
    unrestrictedError_eq_gapRatio_of_le_one 1 (by decide) δ hδ0 hδ1⟩

lemma unrestrictedError_lower_bound (m : ℕ) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    gapRatio δ ^ (2 ^ m) ≤ unrestrictedError m δ := by
  apply le_unrestrictedError
  intro p hp
  exact degree_error_lower_bound δ hδ0 hδ1 (2 ^ m) (by positivity) p
    (program_degree_bound m p hp)

theorem cubic_error_bounds (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    (∀ T : ℕ, gapRatio δ ^ (3 ^ T) ≤ cubicError T δ) ∧
    (∀ T : ℕ, 1 ≤ T → cubicError T δ ≤ gapRatio δ ^ (2 ^ T)) := by
  constructor
  · intro T
    apply le_cubicError
    intro p hp
    exact degree_error_lower_bound δ hδ0 hδ1 (3 ^ T) (by positivity) p
      (cubic_degree_and_cost T p hp).1
  · intro T hT
    exact cubicError_upper_bound T hT δ hδ0 hδ1

lemma cubicError_pos (T : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 < cubicError T δ :=
  (pow_pos (gapRatio_pos hδ0 hδ1) (3 ^ T)).trans_le
    ((cubic_error_bounds δ hδ0 hδ1).1 T)

theorem cubic_error_strictly_decreases (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    StrictAnti (fun T : ℕ => cubicError T δ) := by
  apply strictAnti_nat_of_succ_lt
  intro T
  by_cases hT : T = 0
  · subst T
    exact cubicError_first_strict hδ0 hδ1
  · have hpos := cubicError_pos T δ hδ0 hδ1
    have hlt := cubicError_lt_one T (by omega) δ hδ0 hδ1
    exact (cubicError_square_step T δ hδ0 hδ1 hpos hlt).trans_lt (by nlinarith)

lemma unrestrictedError_le_cubicError (m T : ℕ) (hTm : 2 * T ≤ m)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    unrestrictedError m δ ≤ cubicError T δ := by
  apply le_cubicError
  intro p hp
  exact unrestrictedError_le hδ0 hδ1
    (programComputable_mono hTm (cubic_degree_and_cost T p hp).2)

#assert_trust kernel unrestricted_error_small_budgets
#print axioms unrestricted_error_small_budgets
#assert_trust kernel cubic_error_bounds
#print axioms cubic_error_bounds
#assert_trust kernel cubic_error_strictly_decreases
#print axioms cubic_error_strictly_decreases

end NLA.MF02
