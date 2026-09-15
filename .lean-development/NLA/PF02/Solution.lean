/-
Copyright (c) 2026 George Stepaniants. Apache 2.0.
Mathematical counterexample: Matthew J. Colbrook, Department of Applied Mathematics
and Theoretical Physics, University of Cambridge.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
AI-assisted formalization. This solution never imports the independent Challenge.
-/
import NLA.PF02.QuotientSeparation

set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.PF02
#assert_trust kernel congruence_semantics
#print axioms congruence_semantics
#assert_trust kernel quotient_topology_semantics
#print axioms quotient_topology_semantics
#assert_trust kernel witness_certificates
#print axioms witness_certificates
#assert_trust kernel witness_psd_rank
#print axioms witness_psd_rank
#assert_trust kernel witness_orientations
#print axioms witness_orientations
#assert_trust kernel congruence_coordinate_determinant
#print axioms congruence_coordinate_determinant
#assert_trust kernel orientation_ne_zero
#print axioms orientation_ne_zero
#assert_trust kernel orientation_invariant
#print axioms orientation_invariant
#assert_trust kernel quotient_orientation_separation
#print axioms quotient_orientation_separation
#assert_trust kernel witness_orbit_disconnected
#print axioms witness_orbit_disconnected
#assert_trust kernel not_minimalPSDOrbitConnectedConjecture
#print axioms not_minimalPSDOrbitConnectedConjecture
end NLA.PF02
