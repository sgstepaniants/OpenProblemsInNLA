/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization of Matthew J. Colbrook's SF-01 result, Cambridge DAMTP.

The exact half certificate is consumed by initial_data_valid. There is no
parameter interval, eigenvalue approximation or iteration enumeration.
-/
import NLA.SF01.Definitions
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SF01
noncomputable section

theorem half_positive_certificate : (0 : ℝ) < 1 / 2 := by
  interval_decide (trust := kernel)

lemma half_coefficient_positive (a : ℝ) (ha : 0 < a) : 0 < a / 2 := by
  have h := mul_pos ha half_positive_certificate
  simpa only [one_div, div_eq_mul_inv] using h

theorem initial_data_valid : ValidData initialData := by
  refine ⟨half_positive_certificate, half_positive_certificate, ?_, ?_⟩
  · intro j
    exact Fin.elim0 j
  · intro j
    exact Fin.elim0 j

#print axioms half_positive_certificate
#assert_trust kernel half_positive_certificate
#print axioms initial_data_valid
#assert_trust kernel initial_data_valid

end
end NLA.SF01
