/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

Complete the admissible pivot prefix by genuine GEPP on the nonsingular input.
The target stage is preserved exactly and, with unit input maximum, forces
attainment of the universal sharp bound.
-/
import NLA.IE13.WitnessDynamics
import NLA.IE13.WitnessEntries
import NLA.IE13.Prefix
import NLA.IE13.UpperBound

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.IE13

theorem witness_attainment (p q : ℕ) (hp : 0 < p) :
    ∃ path : PivotPath (witnessOrder p q),
      AdmissiblePath (witnessMatrix p q) path ∧
      (∀ k : Fin (witnessOrder p q), k.val < p + q → path k = witnessSeedPath p q k) ∧
      growth (witnessMatrix p q) path = sharpBound p q := by
  have hn : 1 ≤ witnessOrder p q := by unfold witnessOrder; omega
  have hT : p + q ≤ witnessOrder p q := by unfold witnessOrder; omega
  have hdet := witness_nonsingular p q hp
  obtain ⟨path, hpath, hagree, htrajectory⟩ := admissiblePrefix_extension hn
    (witnessMatrix p q) hdet (witnessSeedPath p q) (p + q) hT
    (witness_prefix_admissible p q hp)
  refine ⟨path, hpath, hagree, le_antisymm ?_ ?_⟩
  · exact universal_growth hn p q (witnessMatrix p q)
      ⟨hdet, (witness_structure p q hp).2.1⟩ path hpath
  · have hentry := (growth_semantics hn (witnessMatrix p q) hdet path).2.1
      (witnessTarget p q) (witnessTarget p q) (witnessTarget p q) le_rfl le_rfl
    change ‖trajectory (witnessMatrix p q) path (p + q)
      (witnessTarget p q) (witnessTarget p q)‖ ≤
        growth (witnessMatrix p q) path * entryMax (witnessMatrix p q) at hentry
    rw [htrajectory (p + q) le_rfl, witness_target_value p q hp,
      Complex.norm_natCast, witness_input_max, mul_one] at hentry
    simpa only [sharpBound, if_neg (Nat.ne_of_gt hp)] using hentry

#print axioms witness_attainment
#assert_trust kernel witness_attainment

end NLA.IE13
