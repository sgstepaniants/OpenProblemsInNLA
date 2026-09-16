/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The original finite zero extension supplies the three left and one right
boundary values. No boundary value for the unused variable v_n is imposed.
-/
import NLA.MF22.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open scoped BigOperators

lemma coordinate_at {n : ℕ} (x : BlockVector n) (j : Fin n) (c : Fin 2) :
    coordinate x (j.val : ℤ) c = x (j, c) := by
  classical
  unfold coordinate
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have hk : (k.val : ℤ) ≠ (j.val : ℤ) := by
      intro he
      apply hkj
      apply Fin.ext
      exact_mod_cast he
    simp [hk]
  · simp

lemma coordinate_outside {n : ℕ} (x : BlockVector n) (j : ℤ) (c : Fin 2)
    (hj : j < 0 ∨ (n : ℤ) ≤ j) : coordinate x j c = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro k _
  have hk : (k.val : ℤ) ≠ j := by
    have hkn := k.isLt
    omega
  simp [hk]

lemma coordinate_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (x : ι → BlockVector n) (j : ℤ) (c : Fin 2) :
    coordinate (∑ i ∈ s, x i) j c = ∑ i ∈ s, coordinate (x i) j c := by
  classical
  simp only [coordinate, Finset.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (k.val : ℤ) = j <;> simp [hk]

theorem source_boundaries (n : ℕ) (hn : 1 ≤ n) (x : BlockVector n) :
    coordinate x (-1) 0 = 0 ∧ coordinate x (-1) 1 = 0 ∧
    coordinate x (-2) 1 = 0 ∧ coordinate x (n : ℤ) 0 = 0 ∧
    sourceState x 0 = (coordinate x 0 0) • boundaryVector ∧
    sourceState x n 0 = 0 := by
  have hm10 := coordinate_outside x (-1) 0 (Or.inl (by norm_num))
  have hm11 := coordinate_outside x (-1) 1 (Or.inl (by norm_num))
  have hm21 := coordinate_outside x (-2) 1 (Or.inl (by norm_num))
  have hright := coordinate_outside x (n : ℤ) 0 (Or.inr le_rfl)
  refine ⟨hm10, hm11, hm21, hright, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [sourceState, boundaryVector, hm10, hm11, hm21]
  · exact hright

#assert_trust kernel source_boundaries
#print axioms source_boundaries

end NLA.MF22
