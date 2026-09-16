/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The sole fixed numerical certificate is exp(1) <= 3. All rank-dependent
parameters, pivots, histories and spectral bounds are handled symbolically.
-/
import NLA.RA02.Definitions
import Mathlib.Analysis.Complex.Exponential
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section

theorem exp_one_bound : Real.exp 1 ≤ 3 := by
  interval_decide (trust := kernel)

/-- Symbolic rank-dependent denominator bound consuming the single certificate. -/
lemma rank_denominator_le_three (r : ℕ) : (1 + 1 / (r : ℝ)) ^ r ≤ 3 := by
  calc
    (1 + 1 / (r : ℝ)) ^ r ≤ Real.exp 1 := by
      simpa only [one_div] using (Real.one_add_inv_pow_le_exp (n := r))
    _ ≤ 3 := exp_one_bound

#print axioms exp_one_bound
#assert_trust kernel exp_one_bound
#print axioms rank_denominator_le_three
#assert_trust kernel rank_denominator_le_three

end
end NLA.RA02
