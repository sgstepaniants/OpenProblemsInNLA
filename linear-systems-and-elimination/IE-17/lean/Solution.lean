/-
IE-17: all 17 exact frozen Challenge targets are supplied by the imported
proof modules. The isolated Challenge is never imported by this solution.

Original mathematics: Matthew J. Colbrook, Department of Applied Mathematics
and Theoretical Physics, University of Cambridge.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
AI-assisted proof implementation and independent AI-agent reviews are
distinct from external human peer review and kernel checking.
-/
import NLA.IE17.Final

set_option autoImplicit false
set_option leancert.trust "kernel"
namespace NLA.IE17

#assert_trust kernel euclideanNorm_sq
#assert_trust kernel backwardError_isLeast
#assert_trust kernel backwardError_zero_at_solution
#assert_trust kernel augmentedPseudoinverse_spec
#assert_trust kernel projectionError_sq_formula
#assert_trust kernel witness_full_column_rank
#assert_trust kernel witness_iterates
#assert_trust kernel witness_before_termination
#assert_trust kernel upperPerturbation_certificate
#assert_trust kernel lowerCertificate_positive
#assert_trust kernel every_second_perturbation_large
#assert_trust kernel witness_backwardError_separation
#assert_trust kernel witness_projectionError_exact
#assert_trust kernel witness_projectionError_separation
#assert_trust kernel counterexample
#assert_trust kernel not_spectralMonotonicity
#assert_trust kernel not_projectionMonotonicity

#print axioms euclideanNorm_sq
#print axioms backwardError_isLeast
#print axioms backwardError_zero_at_solution
#print axioms augmentedPseudoinverse_spec
#print axioms projectionError_sq_formula
#print axioms witness_full_column_rank
#print axioms witness_iterates
#print axioms witness_before_termination
#print axioms upperPerturbation_certificate
#print axioms lowerCertificate_positive
#print axioms every_second_perturbation_large
#print axioms witness_backwardError_separation
#print axioms witness_projectionError_exact
#print axioms witness_projectionError_separation
#print axioms counterexample
#print axioms not_spectralMonotonicity
#print axioms not_projectionMonotonicity

end NLA.IE17
