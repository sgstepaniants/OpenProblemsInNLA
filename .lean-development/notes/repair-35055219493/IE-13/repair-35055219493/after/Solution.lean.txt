/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

Complete IE-13 proof environment. The independent Challenge module is never
imported. The commands check every frozen public theorem for permitted axioms.
This source is an uncompiled candidate until actual Linux evidence is accepted.
-/
import NLA.IE13.Sharp

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.IE13

#print axioms gepp_model_semantics
#assert_trust kernel gepp_model_semantics
#print axioms entryMax_semantics
#assert_trust kernel entryMax_semantics
#print axioms activeMax_semantics
#assert_trust kernel activeMax_semantics
#print axioms growth_semantics
#assert_trust kernel growth_semantics
#print axioms admissiblePath_exists
#assert_trust kernel admissiblePath_exists
#print axioms admissiblePrefix_extension
#assert_trust kernel admissiblePrefix_extension
#print axioms originalRow_update
#assert_trust kernel originalRow_update
#print axioms multiplier_bounds
#assert_trust kernel multiplier_bounds
#print axioms front_structure
#assert_trust kernel front_structure
#print axioms front_transition
#assert_trust kernel front_transition
#print axioms recurrence_history
#assert_trust kernel recurrence_history
#print axioms sequence_recurrence
#assert_trust kernel sequence_recurrence
#print axioms sequence_properties
#assert_trust kernel sequence_properties
#print axioms envelope_recurrence
#assert_trust kernel envelope_recurrence
#print axioms late_column_zero
#assert_trust kernel late_column_zero
#print axioms column_front_bound
#assert_trust kernel column_front_bound
#print axioms all_active_entries_bound
#assert_trust kernel all_active_entries_bound
#print axioms zero_lower_bandwidth
#assert_trust kernel zero_lower_bandwidth
#print axioms universal_growth
#assert_trust kernel universal_growth
#print axioms witness_scale
#assert_trust kernel witness_scale
#print axioms witness_structure
#assert_trust kernel witness_structure
#print axioms witness_prefix_order
#assert_trust kernel witness_prefix_order
#print axioms witness_prefix_admissible
#assert_trust kernel witness_prefix_admissible
#print axioms witness_target_value
#assert_trust kernel witness_target_value
#print axioms witness_nonsingular
#assert_trust kernel witness_nonsingular
#print axioms witness_attainment
#assert_trust kernel witness_attainment
#print axioms identity_attainment
#assert_trust kernel identity_attainment
#print axioms sharp_growth
#assert_trust kernel sharp_growth

end NLA.IE13
