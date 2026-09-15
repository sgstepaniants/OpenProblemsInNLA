/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Full IE-17 negative resolution: both original optimization/projection-defined
errors strictly increase at successive genuine nonzero LSMR iterates.
Original mathematics: Matthew J. Colbrook, University of Cambridge.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
-/
import NLA.IE17.Iterates
import NLA.IE17.Projection
import NLA.IE17.LowerBound

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical Matrix.Norms.L2Operator
noncomputable section
namespace NLA.IE17

theorem counterexample :
    SuccessiveNonzeroIterates witnessA witnessB 1 witnessX1 witnessX2 ∧
    backwardError witnessA witnessB witnessX1 < backwardError witnessA witnessB witnessX2 ∧
    projectionError witnessA witnessB witnessX1 < projectionError witnessA witnessB witnessX2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨by decide, (witness_iterates.2.1 witnessX1).mpr rfl,
      (witness_iterates.2.2.1 witnessX2).mpr rfl, witness_before_termination.1,
      witness_before_termination.2.1, witness_before_termination.2.2.2.1⟩
  · apply (sq_lt_sq₀ (backwardError_nonneg _ _ _) (backwardError_nonneg _ _ _)).mp
    exact lt_of_le_of_lt witness_backwardError_separation.1
      (witness_backwardError_separation.2.1.trans witness_backwardError_separation.2.2)
  · apply (sq_lt_sq₀ (projectionError_nonneg _ _ _) (projectionError_nonneg _ _ _)).mp
    exact witness_projectionError_separation.1.trans
      (witness_projectionError_separation.2.1.trans witness_projectionError_separation.2.2)

theorem not_spectralMonotonicity : ¬ SpectralMonotonicity := by
  intro h
  exact (not_le_of_gt counterexample.2.1)
    (h 4 3 witnessA witnessB 1 witnessX1 witnessX2 counterexample.1)

theorem not_projectionMonotonicity : ¬ ProjectionMonotonicity := by
  intro h
  exact (not_le_of_gt counterexample.2.2)
    (h 4 3 witnessA witnessB 1 witnessX1 witnessX2 counterexample.1)

#assert_trust kernel counterexample
#assert_trust kernel not_spectralMonotonicity
#assert_trust kernel not_projectionMonotonicity
#print axioms counterexample
#print axioms not_spectralMonotonicity
#print axioms not_projectionMonotonicity

end NLA.IE17
