/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Complete independently specified MI-04 target graph. This file imports only
proved implementation modules, never the independent Challenge environment.
-/
import NLA.MI04.Conclusion

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MI04

#print axioms topValue_maximum
#assert_trust kernel topValue_maximum
#print axioms positive_quadratic_iff
#assert_trust kernel positive_quadratic_iff
#print axioms positive_norm_eq_top
#assert_trust kernel positive_norm_eq_top
#print axioms shifted_topValue
#assert_trust kernel shifted_topValue
#print axioms scalar_order_iff_top
#assert_trust kernel scalar_order_iff_top
#print axioms unitary_topValue
#assert_trust kernel unitary_topValue
#print axioms simple_peak_sandwich
#assert_trust kernel simple_peak_sandwich
#print axioms simple_peak_second_order
#assert_trust kernel simple_peak_second_order
#print axioms pencil_isHermitian
#assert_trust kernel pencil_isHermitian
#print axioms universal_to_extreme_symmetry
#assert_trust kernel universal_to_extreme_symmetry
#print axioms extreme_symmetry_scaled_unitary
#assert_trust kernel extreme_symmetry_scaled_unitary
#print axioms weighted_magnitude_identity
#assert_trust kernel weighted_magnitude_identity
#print axioms offDiagonal_magnitude_symmetry
#assert_trust kernel offDiagonal_magnitude_symmetry
#print axioms orthonormal_pair_symmetry
#assert_trust kernel orthonormal_pair_symmetry
#print axioms pair_symmetry_normal
#assert_trust kernel pair_symmetry_normal
#print axioms normal_unitary_diagonalization
#assert_trust kernel normal_unitary_diagonalization
#print axioms pair_symmetry_unitary
#assert_trust kernel pair_symmetry_unitary
#print axioms diagonal_pair_collinearity
#assert_trust kernel diagonal_pair_collinearity
#print axioms collinear_values_affine
#assert_trust kernel collinear_values_affine
#print axioms pair_symmetry_essentially_hermitian
#assert_trust kernel pair_symmetry_essentially_hermitian
#print axioms universal_positive_block_essentially_hermitian
#assert_trust kernel universal_positive_block_essentially_hermitian

end NLA.MI04
