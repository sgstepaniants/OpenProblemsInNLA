/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical proof:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Proposed full export module; all eighteen frozen targets are retained.
-/
import NLA.MF07.Final

set_option autoImplicit false
set_option leancert.trust "kernel"

#check NLA.MF07.matrix_product_semantics
#print axioms NLA.MF07.matrix_product_semantics
#assert_trust kernel NLA.MF07.matrix_product_semantics

#check NLA.MF07.diagonal_inverse
#print axioms NLA.MF07.diagonal_inverse
#assert_trust kernel NLA.MF07.diagonal_inverse

#check NLA.MF07.family_norm_maximum
#print axioms NLA.MF07.family_norm_maximum
#assert_trust kernel NLA.MF07.family_norm_maximum

#check NLA.MF07.family_growth_maximum
#print axioms NLA.MF07.family_growth_maximum
#assert_trust kernel NLA.MF07.family_growth_maximum

#check NLA.MF07.family_growth_submultiplicative
#print axioms NLA.MF07.family_growth_submultiplicative
#assert_trust kernel NLA.MF07.family_growth_submultiplicative

#check NLA.MF07.radius_one_semantics
#print axioms NLA.MF07.radius_one_semantics
#assert_trust kernel NLA.MF07.radius_one_semantics

#check NLA.MF07.identity_family_semantics
#print axioms NLA.MF07.identity_family_semantics
#assert_trust kernel NLA.MF07.identity_family_semantics

#check NLA.MF07.approximate_extremal_norm
#print axioms NLA.MF07.approximate_extremal_norm
#assert_trust kernel NLA.MF07.approximate_extremal_norm

#check NLA.MF07.rounded_extremal_norm
#print axioms NLA.MF07.rounded_extremal_norm
#assert_trust kernel NLA.MF07.rounded_extremal_norm

#check NLA.MF07.triangular_damping
#print axioms NLA.MF07.triangular_damping
#assert_trust kernel NLA.MF07.triangular_damping

#check NLA.MF07.interspersed_product_bound
#print axioms NLA.MF07.interspersed_product_bound
#assert_trust kernel NLA.MF07.interspersed_product_bound

#check NLA.MF07.quantitative_comparison
#print axioms NLA.MF07.quantitative_comparison
#assert_trust kernel NLA.MF07.quantitative_comparison

#check NLA.MF07.scalar_family_growth
#print axioms NLA.MF07.scalar_family_growth
#assert_trust kernel NLA.MF07.scalar_family_growth

#check NLA.MF07.exp_one_bound
#print axioms NLA.MF07.exp_one_bound
#assert_trust kernel NLA.MF07.exp_one_bound

#check NLA.MF07.comparison_threshold_bound
#print axioms NLA.MF07.comparison_threshold_bound
#assert_trust kernel NLA.MF07.comparison_threshold_bound

#check NLA.MF07.growth_constant_positive
#print axioms NLA.MF07.growth_constant_positive
#assert_trust kernel NLA.MF07.growth_constant_positive

#check NLA.MF07.radius_one_growth
#print axioms NLA.MF07.radius_one_growth
#assert_trust kernel NLA.MF07.radius_one_growth

#check NLA.MF07.canonical_uniform_bound
#print axioms NLA.MF07.canonical_uniform_bound
#assert_trust kernel NLA.MF07.canonical_uniform_bound
