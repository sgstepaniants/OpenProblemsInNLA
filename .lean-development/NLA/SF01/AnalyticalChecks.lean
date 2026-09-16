/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Partial analytical-prefix commands only, not a complete Solution. These
commands request future kernel checks; their source is not evidence of a run.
-/
import NLA.SF01.FoundationChecks
import NLA.SF01.SpectralMWeight

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SF01

#print axioms unit_weightVector_equation
#assert_trust kernel unit_weightVector_equation
#print axioms unit_inverse_continuousAt
#assert_trust kernel unit_inverse_continuousAt
#print axioms unit_weightVector_continuousAt
#assert_trust kernel unit_weightVector_continuousAt
#print axioms spectralHomotopy_weight_continuousOn
#assert_trust kernel spectralHomotopy_weight_continuousOn
#print axioms spectralHomotopy_nonnegative_no_zero
#assert_trust kernel spectralHomotopy_nonnegative_no_zero
#print axioms continuous_positive_coordinates
#assert_trust kernel continuous_positive_coordinates
#print axioms spectralHomotopy_weight_positive
#assert_trust kernel spectralHomotopy_weight_positive
#print axioms spectralM_positive_weight
#assert_trust kernel spectralM_positive_weight

end NLA.SF01
