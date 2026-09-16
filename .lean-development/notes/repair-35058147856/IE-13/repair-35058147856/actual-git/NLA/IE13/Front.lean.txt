/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

The general-band front follows from the actual trajectory. No front cardinality
or untouched-row property is an input assumption in the public theorem.
-/
import NLA.IE13.Origin

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.IE13

def FutureRows {n : ℕ} (p : ℕ) (A : Mat n) (path : PivotPath n) (k : ℕ) : Prop :=
  ∀ i : Fin n, k + p ≤ i.val → OriginalRowActive path k i ∧
    ∀ j : Fin n, k ≤ j.val → originalRowStage A path k i j = A i j

lemma oldRows_initial_card {n : ℕ} (p : ℕ) (path : PivotPath n) :
    (oldRows p path 0).card ≤ p := by
  classical
  have hmap : Set.MapsTo (fun i : Fin n => i.val)
      (oldRows p path 0 : Set (Fin n)) (Finset.range p : Set ℕ) := by
    intro i hi
    apply Finset.mem_range.mpr
    simpa only [Nat.zero_add] using (Finset.mem_filter.mp hi).2.2
  have hinj : (oldRows p path 0 : Set (Fin n)).InjOn Fin.val := by
    intro i _ j _ h
    exact Fin.ext h
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn Fin.val hmap hinj

lemma frontRows_card_le {n : ℕ} (p k : ℕ) (path : PivotPath n) :
    (frontRows p path k).card ≤ (oldRows p path k).card + 1 := by
  classical
  by_cases hf : k + p < n
  · let fresh : Fin n := ⟨k + p, hf⟩
    have hsub : frontRows p path k ⊆ insert fresh (oldRows p path k) := by
      intro i hi
      obtain ⟨ha, hle⟩ := (Finset.mem_filter.mp hi).2
      by_cases hlt : i.val < k + p
      · apply Finset.mem_insert_of_mem
        simp only [oldRows, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨ha, hlt⟩
      · have he : i = fresh := Fin.ext (by dsimp [fresh]; omega)
        rw [he]
        exact Finset.mem_insert_self fresh _
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  · have hsub : frontRows p path k ⊆ oldRows p path k := by
      intro i hi
      obtain ⟨ha, hle⟩ := (Finset.mem_filter.mp hi).2
      simp only [oldRows, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ha, by have hi' := i.isLt; omega⟩
    exact (Finset.card_le_card hsub).trans (Nat.le_succ _)

lemma pivot_front_of_future {n : ℕ} (p q : ℕ) (A : Mat n) (hA : Banded p q A)
    (path : PivotPath n) (hpath : AdmissiblePath A path) (k : Fin n)
    (hfuture : FutureRows p A path k.val) :
    pivotLabel path k ∈ frontRows p path k.val := by
  have hactive : OriginalRowActive path k.val (pivotLabel path k) := by
    simpa only [OriginalRowActive, inverse_origin_pivot] using
      (Fin.le_iff_val_le_val.mp (hpath k).1)
  have hlabel : (pivotLabel path k).val ≤ k.val + p := by
    by_contra hnot
    have hlarge : k.val + p < (pivotLabel path k).val := lt_of_not_ge hnot
    have hvalue := (hfuture (pivotLabel path k) hlarge.le).2 k le_rfl
    have hzero : A (pivotLabel path k) k = 0 := hA _ _ (Or.inl hlarge)
    have he : trajectory A path k.val (path k) k = 0 := by
      simpa only [originalRowStage, inverse_origin_pivot, hzero] using hvalue
    exact (hpath k).2.1 he
  simp only [frontRows, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hactive, hlabel⟩

lemma futureRows_advance {n : ℕ} (p q : ℕ) (A : Mat n) (hA : Banded p q A)
    (path : PivotPath n) (hpath : AdmissiblePath A path) (k : Fin n)
    (hfuture : FutureRows p A path k.val) :
    FutureRows p A path (k.val + 1) := by
  classical
  have hpivot := pivot_front_of_future p q A hA path hpath k hfuture
  have hlabel := (Finset.mem_filter.mp hpivot).2.2
  intro i hi
  have hprior := hfuture i (by omega)
  have hne : i ≠ pivotLabel path k := by
    intro he
    have hv := congrArg Fin.val he
    omega
  refine ⟨(originalRowActive_succ_iff path k i (hpath k).1).mpr ⟨hprior.1, hne⟩, ?_⟩
  intro j hj
  have hstep := (originalRow_update A path hpath k i j hprior.1 hne
    (by change k.val < j.val; omega)).2
  have hzero : A i k = 0 := hA i k (Or.inl (by omega))
  rw [hstep, hprior.2 j (by omega), hprior.2 k le_rfl, hzero,
    zero_div, zero_mul, sub_zero]

lemma front_invariant {n : ℕ} (p q : ℕ) (A : Mat n) (hA : Banded p q A)
    (path : PivotPath n) (hpath : AdmissiblePath A path)
    (k : ℕ) (hk : k ≤ n) :
    (oldRows p path k).card ≤ p ∧ FutureRows p A path k := by
  induction k with
  | zero =>
    refine ⟨oldRows_initial_card p path, ?_⟩
    intro i hi
    refine ⟨Nat.zero_le _, ?_⟩
    intro j hj
    rfl
  | succ k ih =>
    have hkn : k < n := by omega
    have hprev := ih (by omega)
    let z : Fin n := ⟨k, hkn⟩
    have hpivot := pivot_front_of_future p q A hA path hpath z hprev.2
    have hcard := frontRows_card_le p k path
    have herase := Finset.card_erase_add_one hpivot
    change ((frontRows p path k).erase (pivotLabel path z)).card + 1 =
      (frontRows p path k).card at herase
    have hnext : oldRows p path (k + 1) =
        (frontRows p path k).erase (pivotLabel path z) :=
      oldRows_succ_eq p path z (hpath z).1
    refine ⟨?_, futureRows_advance p q A hA path hpath z hprev.2⟩
    rw [hnext]
    have hold := hprev.1
    omega

theorem front_structure {n : ℕ} (p q : ℕ) (A : Mat n) (hA : Banded p q A)
    (path : PivotPath n) (hpath : AdmissiblePath A path) (k : Fin n) :
    (oldRows p path k.val).card ≤ p ∧
    (∀ i : Fin n, k.val + p ≤ i.val →
      OriginalRowActive path k.val i ∧
        ∀ j : Fin n, k ≤ j → originalRowStage A path k.val i j = A i j) ∧
    pivotLabel path k ∈ frontRows p path k.val := by
  have h := front_invariant p q A hA path hpath k.val k.isLt.le
  exact ⟨h.1, h.2, pivot_front_of_future p q A hA path hpath k h.2⟩

#print axioms front_structure
#assert_trust kernel front_structure

end NLA.IE13
