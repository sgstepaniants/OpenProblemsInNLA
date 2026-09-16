/-
Partial foundation batch only: this module does not prove all SF-01 contracts
and is not a Solution or a complete-problem verification entry point.
-/
import NLA.SF01.Numerical
import NLA.SF01.SpectralHomotopy
import NLA.SF01.WeightedZReuse

set_option autoImplicit false

#print axioms NLA.SF01.half_positive_certificate
#assert_trust kernel NLA.SF01.half_positive_certificate
#print axioms NLA.SF01.initial_data_valid
#assert_trust kernel NLA.SF01.initial_data_valid
#print axioms NLA.SF01.complex_spectral_radius_semantics
#assert_trust kernel NLA.SF01.complex_spectral_radius_semantics
#print axioms NLA.SF01.spectral_radius_strict_bound
#assert_trust kernel NLA.SF01.spectral_radius_strict_bound
#print axioms NLA.SF01.spectral_homotopy_isUnit
#assert_trust kernel NLA.SF01.spectral_homotopy_isUnit

#print axioms NLA.SF01.complexify_isUnit_iff
#assert_trust kernel NLA.SF01.complexify_isUnit_iff
#print axioms NLA.SF01.weightedZ_maximum_principle
#assert_trust kernel NLA.SF01.weightedZ_maximum_principle
#print axioms NLA.SF01.weightedZ_isUnit
#assert_trust kernel NLA.SF01.weightedZ_isUnit
#print axioms NLA.SF01.weightedZ_inverse_nonnegative
#assert_trust kernel NLA.SF01.weightedZ_inverse_nonnegative
#print axioms NLA.SF01.weightedZ_weightVector_equation
#assert_trust kernel NLA.SF01.weightedZ_weightVector_equation
