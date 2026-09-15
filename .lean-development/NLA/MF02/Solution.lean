/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

This entry point imports proved declarations only, never the independent
Challenge environment. All thirteen reviewed exports are checked below.
-/
import NLA.MF02.Minimum

set_option autoImplicit false
set_option leancert.trust "kernel"

#assert_trust kernel NLA.MF02.uniform_error_is_maximum
#assert_trust kernel NLA.MF02.program_degree_bound
#assert_trust kernel NLA.MF02.cubic_degree_and_cost
#assert_trust kernel NLA.MF02.degree_error_lower_bound
#assert_trust kernel NLA.MF02.optimized_cubic_interval
#assert_trust kernel NLA.MF02.optimized_cubic_ratio
#assert_trust kernel NLA.MF02.cubic_error_bounds
#assert_trust kernel NLA.MF02.cubic_error_strictly_decreases
#assert_trust kernel NLA.MF02.unrestricted_error_small_budgets
#assert_trust kernel NLA.MF02.stage_minimum_attained
#assert_trust kernel NLA.MF02.stage_minimum_small_budgets
#assert_trust kernel NLA.MF02.stage_minimum_bounds
#assert_trust kernel NLA.MF02.uniform_asymptotic_order

#print axioms NLA.MF02.uniform_error_is_maximum
#print axioms NLA.MF02.program_degree_bound
#print axioms NLA.MF02.cubic_degree_and_cost
#print axioms NLA.MF02.degree_error_lower_bound
#print axioms NLA.MF02.optimized_cubic_interval
#print axioms NLA.MF02.optimized_cubic_ratio
#print axioms NLA.MF02.cubic_error_bounds
#print axioms NLA.MF02.cubic_error_strictly_decreases
#print axioms NLA.MF02.unrestricted_error_small_budgets
#print axioms NLA.MF02.stage_minimum_attained
#print axioms NLA.MF02.stage_minimum_small_budgets
#print axioms NLA.MF02.stage_minimum_bounds
#print axioms NLA.MF02.uniform_asymptotic_order
