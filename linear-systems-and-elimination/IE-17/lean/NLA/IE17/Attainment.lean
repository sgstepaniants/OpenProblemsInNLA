/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

The minimum is taken over every feasible real perturbation. Compactness is
used only after truncating at the norm of the always-feasible perturbation -A.
-/
import NLA.IE17.Geometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
open scoped BigOperators Classical Matrix.Norms.L2Operator
noncomputable section
namespace NLA.IE17

theorem feasiblePerturbations_isClosed {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    IsClosed {E : Mat m n | FeasiblePerturbation A b x E} := by
  have hf : Continuous (fun E : Mat m n =>
      (A + E).transpose.mulVec ((A + E).mulVec x - b)) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  exact isClosed_eq hf continuous_const

theorem backwardError_isLeast {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    IsLeast (feasibleNorms A b x) (backwardError A b x) := by
  let S : Set (Mat m n) :=
    {E | FeasiblePerturbation A b x E ∧ spectralNorm E ≤ spectralNorm (-A)}
  have hS : IsCompact S := by
    have hrepr : S = Metric.closedBall 0 (spectralNorm (-A)) ∩
        {E : Mat m n | FeasiblePerturbation A b x E} := by
      ext E
      simp [S, Metric.mem_closedBall, dist_zero_right, spectralNorm, and_comm]
    rw [hrepr]
    exact (isCompact_closedBall _ _).inter_right (feasiblePerturbations_isClosed A b x)
  have hnonempty : S.Nonempty := ⟨-A, neg_self_feasible A b x, le_rfl⟩
  have hcontinuous : ContinuousOn (spectralNorm : Mat m n → ℝ) S :=
    continuous_norm.continuousOn
  obtain ⟨E₀, hE₀, hmin⟩ := hS.exists_isMinOn hnonempty hcontinuous
  have hleast : IsLeast (feasibleNorms A b x) (spectralNorm E₀) := by
    refine ⟨⟨E₀, hE₀.1, rfl⟩, ?_⟩
    rintro c ⟨E, hE, rfl⟩
    by_cases hbound : spectralNorm E ≤ spectralNorm (-A)
    · exact hmin ⟨hE, hbound⟩
    · exact hE₀.2.trans (le_of_lt (lt_of_not_ge hbound))
  have heq : backwardError A b x = spectralNorm E₀ := hleast.csInf_eq
  rwa [heq]

#assert_trust kernel backwardError_isLeast
#print axioms backwardError_isLeast

end NLA.IE17
