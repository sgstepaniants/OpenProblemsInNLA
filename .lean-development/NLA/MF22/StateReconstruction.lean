/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Finite state reconstruction explicitly handles j=0, j=1, and j=n. All
coordinates outside the original vector are its genuine zero extension.
-/
import NLA.MF22.Coordinates
import Mathlib.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22

noncomputable section

def stateCoordinates (n : ℕ) (w : ℕ → Fin 4 → ℂ) : BlockVector n := fun r =>
  if r.2 = 0 then w r.1.val 0 else w (r.1.val + 1) 1

lemma state_coordinate_zero {n : ℕ} (w : ℕ → Fin 4 → ℂ) (j : ℕ) (hj : j < n) :
    coordinate (stateCoordinates n w) (j : ℤ) 0 = w j 0 := by
  simpa [stateCoordinates] using coordinate_at (stateCoordinates n w) ⟨j, hj⟩ 0

lemma state_coordinate_one {n : ℕ} (w : ℕ → Fin 4 → ℂ) (j : ℕ) (hj : j < n) :
    coordinate (stateCoordinates n w) (j : ℤ) 1 = w (j + 1) 1 := by
  simpa [stateCoordinates] using coordinate_at (stateCoordinates n w) ⟨j, hj⟩ 1

lemma reconstruct_state (n : ℕ) (hn : 1 ≤ n) (w : ℕ → Fin 4 → ℂ)
    (hinit : ∀ i : Fin 4, i ≠ 0 → w 0 i = 0) (hterminal : w n 0 = 0)
    (hshift₂ : ∀ j : ℕ, j < n → w (j + 1) 2 = w j 0)
    (hshift₃ : ∀ j : ℕ, j < n → w (j + 1) 3 = w j 1)
    (j : ℕ) (hj : j ≤ n) : sourceState (stateCoordinates n w) j = w j := by
  ext i
  fin_cases i
  · change coordinate (stateCoordinates n w) (j : ℤ) 0 = w j 0
    rcases lt_or_eq_of_le hj with hlt | he
    · exact state_coordinate_zero w j hlt
    · subst j
      rw [coordinate_outside _ _ _ (Or.inr le_rfl), hterminal]
  · change coordinate (stateCoordinates n w) ((j : ℤ) - 1) 1 = w j 1
    cases j with
    | zero =>
        rw [hinit 1 (by decide)]
        exact coordinate_outside _ _ _ (Or.inl (by norm_num))
    | succ j =>
        have hjn : j < n := by omega
        have he : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
        rw [he]
        exact state_coordinate_one w j hjn
  · change coordinate (stateCoordinates n w) ((j : ℤ) - 1) 0 = w j 2
    cases j with
    | zero =>
        rw [hinit 2 (by decide)]
        exact coordinate_outside _ _ _ (Or.inl (by norm_num))
    | succ j =>
        have hjn : j < n := by omega
        have he : ((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ) := by omega
        rw [he, state_coordinate_zero w j hjn, hshift₂ j hjn]
  · change coordinate (stateCoordinates n w) ((j : ℤ) - 2) 1 = w j 3
    cases j with
    | zero =>
        rw [hinit 3 (by decide)]
        exact coordinate_outside _ _ _ (Or.inl (by norm_num))
    | succ j =>
        have hjn : j < n := by omega
        rw [hshift₃ j hjn]
        cases j with
        | zero =>
            rw [hinit 1 (by decide)]
            exact coordinate_outside _ _ _ (Or.inl (by norm_num))
        | succ j =>
            have hjn' : j < n := by omega
            have he : ((j + 1 + 1 : ℕ) : ℤ) - 2 = (j : ℤ) := by omega
            rw [he]
            exact state_coordinate_one w j hjn'

#assert_trust kernel reconstruct_state

end
end NLA.MF22
