/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

One exact kernel interval certificate for the scalar half is consumed by the
all-p scale bounds. Every remaining power identity is symbolic.
-/
import NLA.IE13.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.IE13

lemma half_bounds_certificate : (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) ≤ 1 := by
  constructor <;> interval_decide (trust := kernel)

theorem witness_scale (p : ℕ) :
    0 < (witnessScale p : ℝ) ∧ (witnessScale p : ℝ) ≤ 1 ∧
    (witnessScale p : ℝ) * (2 : ℝ) ^ p = 1 := by
  have hs : (witnessScale p : ℝ) = (1 / 2 : ℝ) ^ p := by
    simp only [witnessScale, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  rw [hs]
  refine ⟨pow_pos half_bounds_certificate.1 p,
    pow_le_one₀ half_bounds_certificate.1.le half_bounds_certificate.2, ?_⟩
  rw [← mul_pow]
  norm_num

lemma witnessScale_ne_zero (p : ℕ) : witnessScale p ≠ 0 := by
  intro h
  have hp := (witness_scale p).1
  rw [h, Rat.cast_zero] at hp
  exact lt_irrefl _ hp

#print axioms half_bounds_certificate
#assert_trust kernel half_bounds_certificate
#print axioms witness_scale
#assert_trust kernel witness_scale

end NLA.IE13
