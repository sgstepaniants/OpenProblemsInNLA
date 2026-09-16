/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

The attained greatest value and real supremum for the complete original set:
all admissible dimensions, nonsingular complex band matrices and legal pivots.
-/
import NLA.IE13.Attainment
import NLA.IE13.Identity

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.IE13

lemma sharpBound_mem_growthValues (p q : ℕ) : sharpBound p q ∈ growthValues p q := by
  by_cases hp : p = 0
  · subst p
    obtain ⟨hinput, hpath, hgrowth⟩ := identity_attainment q
    refine ⟨q + 1, ?_, (1 : Mat (q + 1)), hinput, (fun k => k), hpath, ?_⟩
    · simp only [Nat.zero_max]
      omega
    · simpa only [sharpBound, if_pos rfl] using hgrowth
  · have hpos := Nat.pos_of_ne_zero hp
    obtain ⟨path, hpath, _, hgrowth⟩ := witness_attainment p q hpos
    have hstructure := witness_structure p q hpos
    exact ⟨witnessOrder p q, hstructure.1, witnessMatrix p q,
      ⟨witness_nonsingular p q hpos, hstructure.2.1⟩, path, hpath, hgrowth⟩

lemma growthValues_le_sharpBound (p q : ℕ) : ∀ r ∈ growthValues p q, r ≤ sharpBound p q := by
  intro r hr
  obtain ⟨n, hn, A, hA, path, hpath, hvalue⟩ := hr
  rw [← hvalue]
  exact universal_growth (by omega) p q A hA path hpath

theorem sharp_growth (p q : ℕ) (hne : p ≠ q) :
    IsGreatest (growthValues p q) (sharpBound p q) ∧
    sharpConstant p q = sharpBound p q := by
  have hg : IsGreatest (growthValues p q) (sharpBound p q) :=
    ⟨sharpBound_mem_growthValues p q, growthValues_le_sharpBound p q⟩
  exact ⟨hg, hg.isLUB.csSup_eq ⟨sharpBound p q, hg.1⟩⟩

#print axioms sharp_growth
#assert_trust kernel sharp_growth

end NLA.IE13
