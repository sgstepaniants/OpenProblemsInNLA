/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

Before a late column reaches the moving front, its actual old-row entries
vanish. The proof uses the physical-row update and the original upper band.
-/
import NLA.IE13.Front

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.IE13

lemma oldRows_subset_frontRows {n : ℕ} (p k : ℕ) (path : PivotPath n) :
    oldRows p path k ⊆ frontRows p path k := by
  intro i hi
  obtain ⟨ha, hlt⟩ := (Finset.mem_filter.mp hi).2
  simp only [frontRows, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨ha, hlt.le⟩

lemma front_not_old_label {n : ℕ} (p k : ℕ) (path : PivotPath n) (i : Fin n)
    (hi : i ∈ frontRows p path k) (hnot : i ∉ oldRows p path k) :
    i.val = k + p := by
  obtain ⟨ha, hle⟩ := (Finset.mem_filter.mp hi).2
  have hnlt : ¬i.val < k + p := by
    intro hlt
    apply hnot
    simp only [oldRows, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨ha, hlt⟩
  omega

lemma front_not_old_value {n : ℕ} (p q : ℕ) (A : Mat n) (hA : Banded p q A)
    (path : PivotPath n) (hpath : AdmissiblePath A path) (k i j : Fin n)
    (hi : i ∈ frontRows p path k.val) (hnot : i ∉ oldRows p path k.val)
    (hj : k ≤ j) : originalRowStage A path k.val i j = A i j := by
  have hv := front_not_old_label p k.val path i hi hnot
  exact ((front_structure p q A hA path hpath k).2.1 i (by omega)).2 j hj

lemma late_column_zero_at {n : ℕ} (p q : ℕ) (A : Mat n) (hA : Banded p q A)
    (path : PivotPath n) (hpath : AdmissiblePath A path) (k : ℕ) (j : Fin n)
    (hlate : k + p + q ≤ j.val) :
    ∀ i ∈ oldRows p path k, originalRowStage A path k i j = 0 := by
  revert hlate
  induction k with
  | zero =>
    intro hlate i hi
    have hrow := (Finset.mem_filter.mp hi).2.2
    have hzero := hA i j (Or.inr (by omega : i.val + q < j.val))
    exact hzero
  | succ k ih =>
    intro hlate i hi
    have hkn : k < n := by have hjn := j.isLt; omega
    let z : Fin n := ⟨k, hkn⟩
    have hj : z < j := by change k < j.val; omega
    have hprior := ih (by omega : k + p + q ≤ j.val)
    have hfrontzero : ∀ a ∈ frontRows p path k,
        originalRowStage A path k a j = 0 := by
      intro a ha
      by_cases hold : a ∈ oldRows p path k
      · exact hprior a hold
      · have hv := front_not_old_label p k path a ha hold
        have he := front_not_old_value p q A hA path hpath z a j ha hold hj.le
        rw [he]
        exact hA a j (Or.inr (by omega))
    have hsets := oldRows_succ_eq p path z (hpath z).1
    change oldRows p path (k + 1) =
      (frontRows p path k).erase (pivotLabel path z) at hsets
    rw [hsets] at hi
    obtain ⟨hne, hifront⟩ := Finset.mem_erase.mp hi
    have hactive := (Finset.mem_filter.mp hifront).2.1
    have hstep := (originalRow_update A path hpath z i j hactive hne hj).2
    have hpivot := (front_structure p q A hA path hpath z).2.2
    rw [hstep, hfrontzero i hifront, hfrontzero (pivotLabel path z) hpivot,
      mul_zero, sub_zero]

theorem late_column_zero {n : ℕ} (p q : ℕ) (A : Mat n) (hA : Banded p q A)
    (path : PivotPath n) (hpath : AdmissiblePath A path) (k j : Fin n)
    (hlate : k.val + p + q ≤ j.val) :
    ∀ i ∈ oldRows p path k.val, originalRowStage A path k.val i j = 0 :=
  late_column_zero_at p q A hA path hpath k.val j hlate

#print axioms late_column_zero
#assert_trust kernel late_column_zero

end NLA.IE13
