/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

The generic swap and survivor identities adapt IE-14 Front.lean at immutable
6e48f25fffdae2cf93e4985dc515abbd15e0481b. Its cyclic front is not reused.
All labels here are the actual original rows under the frozen physical swaps.
-/
import NLA.IE13.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.IE13

lemma origin_step {n : ℕ} (path : PivotPath n) (k : ℕ) (hk : k < n) (i : Fin n) :
    origin path (k + 1) i = origin path k (Equiv.swap ⟨k, hk⟩ (path ⟨k, hk⟩) i) := by
  simp only [origin, dif_pos hk, Equiv.trans_apply]

lemma origin_symm_step {n : ℕ} (path : PivotPath n) (k : ℕ) (hk : k < n) (i : Fin n) :
    (origin path (k + 1)).symm i =
      Equiv.swap ⟨k, hk⟩ (path ⟨k, hk⟩) ((origin path k).symm i) := by
  simp only [origin, dif_pos hk, Equiv.symm_trans_apply, Equiv.symm_swap]

lemma swap_survivor_active {n : ℕ} (k p i : Fin n) (hp : k ≤ p)
    (hi : k ≤ i) (hne : i ≠ p) : k < Equiv.swap k p i := by
  have hle := swap_active k p i hp hi
  apply lt_of_le_of_ne hle
  intro he
  have h := congrArg (Equiv.swap k p) he
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_self] at h
  exact hne h.symm

lemma swap_active_after_iff {n : ℕ} (k p i : Fin n) (hp : k ≤ p) :
    k < Equiv.swap k p i ↔ k ≤ i ∧ i ≠ p := by
  constructor
  · intro hi
    have hle := swap_active k p (Equiv.swap k p i) hp hi.le
    simp only [Equiv.swap_apply_self] at hle
    refine ⟨hle, ?_⟩
    intro he
    subst i
    simpa only [Equiv.swap_apply_right, lt_self_iff_false] using hi
  · rintro ⟨hi, hne⟩
    exact swap_survivor_active k p i hp hi hne

@[simp] lemma inverse_origin_pivot {n : ℕ} (path : PivotPath n) (k : Fin n) :
    (origin path k.val).symm (pivotLabel path k) = path k := by
  simp only [pivotLabel, Equiv.symm_apply_apply]

lemma inverse_origin_eq_pivot_iff {n : ℕ} (path : PivotPath n) (k i : Fin n) :
    (origin path k.val).symm i = path k ↔ i = pivotLabel path k := by
  constructor
  · intro h
    have he := congrArg (origin path k.val) h
    simpa only [Equiv.apply_symm_apply, pivotLabel] using he
  · intro h
    rw [h, inverse_origin_pivot]

lemma originalRowActive_succ_iff {n : ℕ} (path : PivotPath n) (k i : Fin n)
    (hp : k ≤ path k) :
    OriginalRowActive path (k.val + 1) i ↔
      OriginalRowActive path k.val i ∧ i ≠ pivotLabel path k := by
  unfold OriginalRowActive
  rw [origin_symm_step path k.val k.isLt]
  change k < Equiv.swap k (path k) ((origin path k.val).symm i) ↔
    k ≤ (origin path k.val).symm i ∧ i ≠ pivotLabel path k
  rw [swap_active_after_iff k (path k) _ hp]
  exact and_congr_right (fun _ => not_congr (inverse_origin_eq_pivot_iff path k i))

lemma trajectory_survivor_entry {n : ℕ} (A : Mat n) (path : PivotPath n)
    (k : ℕ) (hk : k < n) (i j : Fin n)
    (hp : k ≤ (path ⟨k, hk⟩).val) (hi : k ≤ i.val)
    (hne : i ≠ path ⟨k, hk⟩) (hj : k < j.val) :
    trajectory A path (k + 1) (Equiv.swap ⟨k, hk⟩ (path ⟨k, hk⟩) i) j =
      trajectory A path k i j -
        (trajectory A path k i ⟨k, hk⟩ /
          trajectory A path k (path ⟨k, hk⟩) ⟨k, hk⟩) *
        trajectory A path k (path ⟨k, hk⟩) j := by
  have hrow := swap_survivor_active ⟨k, hk⟩ (path ⟨k, hk⟩) i hp hi hne
  rw [trajectory, dif_pos hk]
  change (if (⟨k, hk⟩ : Fin n) < Equiv.swap ⟨k, hk⟩ (path ⟨k, hk⟩) i ∧
      (⟨k, hk⟩ : Fin n) < j then _ else _) = _
  rw [if_pos ⟨hrow, hj⟩]
  unfold rowSwap
  simp only [Equiv.swap_apply_self, Equiv.swap_apply_left]

theorem originalRow_update {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hpath : AdmissiblePath A path) (k i j : Fin n)
    (hi : OriginalRowActive path k.val i) (hne : i ≠ pivotLabel path k) (hj : k < j) :
    OriginalRowActive path (k.val + 1) i ∧
    originalRowStage A path (k.val + 1) i j =
      originalRowStage A path k.val i j -
        (originalRowStage A path k.val i k /
          originalRowStage A path k.val (pivotLabel path k) k) *
        originalRowStage A path k.val (pivotLabel path k) j := by
  have hp := hpath k
  have hneq : (origin path k.val).symm i ≠ path k :=
    fun h => hne ((inverse_origin_eq_pivot_iff path k i).mp h)
  refine ⟨(originalRowActive_succ_iff path k i hp.1).mpr ⟨hi, hne⟩, ?_⟩
  unfold originalRowStage
  rw [origin_symm_step path k.val k.isLt, inverse_origin_pivot]
  exact trajectory_survivor_entry A path k.val k.isLt _ j hp.1 hi hneq hj

theorem multiplier_bounds {n : ℕ} (A : Mat n) (path : PivotPath n)
    (hpath : AdmissiblePath A path) (k i : Fin n)
    (hi : OriginalRowActive path k.val i) :
    originalRowStage A path k.val (pivotLabel path k) k ≠ 0 ∧
    ‖originalRowStage A path k.val i k /
      originalRowStage A path k.val (pivotLabel path k) k‖ ≤ 1 := by
  simp only [originalRowStage, inverse_origin_pivot]
  exact ⟨(hpath k).2.1,
    multiplier_bound (trajectory A path k.val) k (path k) (hpath k)
      ((origin path k.val).symm i) hi⟩

lemma oldRows_succ_eq {n : ℕ} (p : ℕ) (path : PivotPath n) (k : Fin n)
    (hp : k ≤ path k) :
    oldRows p path (k.val + 1) = (frontRows p path k.val).erase (pivotLabel path k) := by
  classical
  ext i
  simp only [oldRows, frontRows, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_erase, originalRowActive_succ_iff path k i hp]
  omega

theorem front_transition {n : ℕ} (p q : ℕ) (A : Mat n) (hA : Banded p q A)
    (path : PivotPath n) (hpath : AdmissiblePath A path) (k : Fin n) :
    oldRows p path (k.val + 1) =
      (frontRows p path k.val).erase (pivotLabel path k) :=
  oldRows_succ_eq p path k (hpath k).1

#print axioms originalRow_update
#assert_trust kernel originalRow_update
#print axioms multiplier_bounds
#assert_trust kernel multiplier_bounds
#print axioms front_transition
#assert_trust kernel front_transition

end NLA.IE13
