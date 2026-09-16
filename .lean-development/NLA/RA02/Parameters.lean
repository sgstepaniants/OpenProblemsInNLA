/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.
-/
import NLA.RA02.Definitions
import Mathlib.Tactic
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section

lemma smallParameter_pos (r : ℕ) : 0 < smallParameter r := by
  unfold smallParameter
  positivity

lemma smallParameter_lt_one (r : ℕ) (hr : 1 ≤ r) : smallParameter r < 1 := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hden : 0 < 2 * (r : ℝ) + 1 := by positivity
  unfold smallParameter
  apply (div_lt_one hden).2
  linarith

lemma scaleParameter_pos (r : ℕ) : 0 < scaleParameter r := by
  exact pow_pos (smallParameter_pos r) _

lemma diagonalWeight_pos (r i : ℕ) : 0 < diagonalWeight r i := by
  exact pow_pos (scaleParameter_pos r) _

lemma couplingWeight_pos (r i : ℕ) : 0 < couplingWeight r i := by
  exact pow_pos (smallParameter_pos r) _

theorem scalar_parameters (r : ℕ) (hr : 1 ≤ r) :
    0 < smallParameter r ∧ smallParameter r < 1 ∧
    0 < scaleParameter r ∧ scaleParameter r ≤ smallParameter r ^ 2 ∧
    smallParameter r ^ 2 < 1 ∧
    ∀ i : ℕ, 0 < diagonalWeight r i ∧ 0 < couplingWeight r i := by
  have ht0 := smallParameter_pos r
  have ht1 := smallParameter_lt_one r hr
  refine ⟨ht0, ht1, scaleParameter_pos r, ?_, ?_, ?_⟩
  · exact pow_le_pow_of_le_one ht0.le ht1.le (by omega : 2 ≤ 2 * (r + 1))
  · exact pow_lt_one₀ ht0.le ht1 (by decide : (2 : ℕ) ≠ 0)
  · intro i
    exact ⟨diagonalWeight_pos r i, couplingWeight_pos r i⟩

#print axioms scalar_parameters
#assert_trust kernel scalar_parameters

end
end NLA.RA02
