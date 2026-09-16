/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Complete MF-22 proof entry point. Every frozen target is imported from the
actual implementation and checked for Lean kernel-only trust. Challenge.lean
is intentionally absent from this environment.
-/
import NLA.MF22.Conditioning

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22

#assert_trust kernel complex_entry_norm_bound
#print axioms complex_entry_norm_bound
#assert_trust kernel source_entry_bound
#print axioms source_entry_bound
#assert_trust kernel leading_block_invertible
#print axioms leading_block_invertible
#assert_trust kernel source_boundaries
#print axioms source_boundaries
#assert_trust kernel source_recurrence
#print axioms source_recurrence
#assert_trust kernel transfer_polynomial_certificates
#print axioms transfer_polynomial_certificates
#assert_trust kernel numerator_denominator_coprime
#print axioms numerator_denominator_coprime
#assert_trust kernel quartic_factorization
#print axioms quartic_factorization
#assert_trust kernel cayley_identity
#print axioms cayley_identity
#assert_trust kernel positive_discriminant_factor
#print axioms positive_discriminant_factor
#assert_trust kernel real_cubic_discriminant
#print axioms real_cubic_discriminant
#assert_trust kernel exceptional_parameter
#print axioms exceptional_parameter
#assert_trust kernel four_roots
#print axioms four_roots
#assert_trust kernel spectral_projector_algebra
#print axioms spectral_projector_algebra
#assert_trust kernel dominant_projector
#print axioms dominant_projector
#assert_trust kernel spectral_tail_bounds
#print axioms spectral_tail_bounds
#assert_trust kernel green_source_state
#print axioms green_source_state
#assert_trust kernel green_inverse
#print axioms green_inverse
#assert_trust kernel uniform_green_entries
#print axioms uniform_green_entries
#assert_trust kernel eventual_inverse_entries
#print axioms eventual_inverse_entries
#assert_trust kernel eventual_quadratic_conditioning
#print axioms eventual_quadratic_conditioning
#assert_trust kernel polynomial_conditioning
#print axioms polynomial_conditioning

end NLA.MF22
