/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematics: Matthew J. Colbrook.

Partial spectral-bridge check commands only. This is not a Solution or
evidence that kernel, numerical, or Comparator checks have executed.
-/
import NLA.SF01.AnalyticalChecks
import NLA.SF01.SpectralMConverse
import NLA.SF01.HWeight

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.SF01

#print axioms complexSpectrum_hasEigenvector
#assert_trust kernel complexSpectrum_hasEigenvector
#print axioms complexify_mulVec_norm_le
#assert_trust kernel complexify_mulVec_norm_le
#print axioms weighted_eigenvector_bound
#assert_trust kernel weighted_eigenvector_bound
#print axioms weighted_complexSpectrum_bound
#assert_trust kernel weighted_complexSpectrum_bound
#print axioms weighted_Z_spectralM
#assert_trust kernel weighted_Z_spectralM
#print axioms comparison_mulVec_row
#assert_trust kernel comparison_mulVec_row
#print axioms weighted_comparison_isUnit
#assert_trust kernel weighted_comparison_isUnit
#print axioms H_positive_weight
#assert_trust kernel H_positive_weight

end NLA.SF01
