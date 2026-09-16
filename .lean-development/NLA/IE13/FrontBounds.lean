/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

The abstract finite-subset inequality is applied to the actual original-label
front. The only possible new label is k+p, and it is unchanged in the input.
-/
import NLA.IE13.LateColumn
import NLA.IE13.SubsetAlgebra

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators
namespace NLA.IE13

lemma front_new_unique {n : ℕ} (p k : ℕ) (path : PivotPath n) :
    ∀ i ∈ frontRows p path k, i ∉ oldRows p path k →
      ∀ j ∈ frontRows p path k, j ∉ oldRows p path k → i = j := by
  intro i hi hio j hj hjo
  apply Fin.ext
  exact (front_not_old_label p k path i hi hio).trans
    (front_not_old_label p k path j hj hjo).symm

lemma front_new_norm {n : ℕ} (p q : ℕ) (A : Mat n) (hA : Banded p q A)
    (path : PivotPath n) (hpath : AdmissiblePath A path) (k j : Fin n) (hj : k ≤ j) :
    ∀ i ∈ frontRows p path k.val, i ∉ oldRows p path k.val →
      ‖originalRowStage A path k.val i j‖ ≤ entryMax A := by
  intro i hi hio
  rw [front_not_old_value p q A hA path hpath k i j hi hio hj]
  exact norm_le_entryMax A i j

lemma front_column_bounds {n : ℕ} (p q t : ℕ) (ht : 1 ≤ t)
    (A : Mat n) (hA : Banded p q A) (path : PivotPath n)
    (hpath : AdmissiblePath A path) (k j : Fin n) (hj : k ≤ j)
    (hbound : ∀ S : Finset (Fin n), S ⊆ oldRows p path k.val →
      (∑ i ∈ S, ‖originalRowStage A path k.val i j‖) ≤
        (envelopeSum p t S.card : ℝ) * entryMax A) :
    (∀ S : Finset (Fin n), S ⊆ frontRows p path k.val → S.card ≤ p →
      (∑ i ∈ S, ‖originalRowStage A path k.val i j‖) ≤
        (envelopeSum p t S.card : ℝ) * entryMax A) ∧
    (∀ S : Finset (Fin n), S ⊆ frontRows p path k.val →
      (∑ i ∈ S, ‖originalRowStage A path k.val i j‖) ≤
        ((envelopeSum p t p + 1 : ℕ) : ℝ) * entryMax A) := by
  have hu := front_new_unique p k.val path
  have hn := front_new_norm p q A hA path hpath k j hj
  have hc := (front_structure p q A hA path hpath k).1
  exact ⟨one_new_small_subset p t ht _ _ _ _ (entryMax_nonneg A) hu hn hbound,
    one_new_full_subset p t _ _ hc _ _ (entryMax_nonneg A) hu hn hbound⟩

lemma old_column_advance_positive {n : ℕ} (p q t : ℕ) (hp : 0 < p) (ht : 1 ≤ t)
    (A : Mat n) (hA : Banded p q A) (path : PivotPath n)
    (hpath : AdmissiblePath A path) (k j : Fin n) (hj : k < j)
    (hbound : ∀ S : Finset (Fin n), S ⊆ oldRows p path k.val →
      (∑ i ∈ S, ‖originalRowStage A path k.val i j‖) ≤
        (envelopeSum p t S.card : ℝ) * entryMax A) :
    ∀ S : Finset (Fin n), S ⊆ oldRows p path (k.val + 1) →
      (∑ i ∈ S, ‖originalRowStage A path (k.val + 1) i j‖) ≤
        (envelopeSum p (t + 1) S.card : ℝ) * entryMax A := by
  classical
  intro S hS
  have hf := front_column_bounds p q t ht A hA path hpath k j hj.le hbound
  have hs : S ⊆ (frontRows p path k.val).erase (pivotLabel path k) := by
    simpa only [front_transition p q A hA path hpath k] using hS
  have hc : S.card ≤ p := (Finset.card_le_card hS).trans
    (front_invariant p q A hA path hpath (k.val + 1) (Nat.succ_le_of_lt k.isLt)).1
  have hμ : ∀ i ∈ S,
      ‖originalRowStage A path k.val i k /
        originalRowStage A path k.val (pivotLabel path k) k‖ ≤ 1 := by
    intro i hi
    have hfront := (Finset.mem_erase.mp (hs hi)).2
    exact (multiplier_bounds A path hpath k i (Finset.mem_filter.mp hfront).2.1).2
  have hb := subset_update_bound p t hp ht (frontRows p path k.val) (pivotLabel path k)
    (front_structure p q A hA path hpath k).2.2
    (fun i => originalRowStage A path k.val i j)
    (fun i => originalRowStage A path k.val i k /
      originalRowStage A path k.val (pivotLabel path k) k)
    (entryMax A) (entryMax_nonneg A) hf.1 hf.2 S hs hc hμ
  calc
    (∑ i ∈ S, ‖originalRowStage A path (k.val + 1) i j‖) =
        ∑ i ∈ S, ‖originalRowStage A path k.val i j -
          (originalRowStage A path k.val i k /
            originalRowStage A path k.val (pivotLabel path k) k) *
          originalRowStage A path k.val (pivotLabel path k) j‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      obtain ⟨hne, hif⟩ := Finset.mem_erase.mp (hs hi)
      rw [(originalRow_update A path hpath k i j
        (Finset.mem_filter.mp hif).2.1 hne hj).2]
    _ ≤ (envelopeSum p (t + 1) S.card : ℝ) * entryMax A := hb

lemma envelopeSum_time_one (p r : ℕ) (hr : r ≤ p) : envelopeSum p 1 r = r := by
  revert hr
  induction r with
  | zero => intro hr; exact envelopeSum_zero p 1
  | succ r ih =>
    intro hr
    have hrp : r < p := by omega
    rw [envelopeSum_succ p 1 r hrp, ih hrp.le, envelope_one]

lemma old_column_advance_zero {n : ℕ} (p q : ℕ)
    (A : Mat n) (hA : Banded p q A) (path : PivotPath n)
    (hpath : AdmissiblePath A path) (k j : Fin n) (hj : k < j)
    (hzero : ∀ i ∈ oldRows p path k.val, originalRowStage A path k.val i j = 0) :
    ∀ S : Finset (Fin n), S ⊆ oldRows p path (k.val + 1) →
      (∑ i ∈ S, ‖originalRowStage A path (k.val + 1) i j‖) ≤
        (envelopeSum p 1 S.card : ℝ) * entryMax A := by
  classical
  intro S hS
  have hs : S ⊆ (frontRows p path k.val).erase (pivotLabel path k) := by
    simpa only [front_transition p q A hA path hpath k] using hS
  have hpivot := (front_structure p q A hA path hpath k).2.2
  have hn : ∀ i ∈ frontRows p path k.val,
      ‖originalRowStage A path k.val i j‖ ≤ entryMax A := by
    intro i hi
    by_cases hold : i ∈ oldRows p path k.val
    · rw [hzero i hold, norm_zero]
      exact entryMax_nonneg A
    · exact front_new_norm p q A hA path hpath k j hj.le i hi hold
  have hnew : ∀ i ∈ S, ‖originalRowStage A path (k.val + 1) i j‖ ≤ entryMax A := by
    intro i hi
    obtain ⟨hne, hif⟩ := Finset.mem_erase.mp (hs hi)
    have hai := (Finset.mem_filter.mp hif).2.1
    rw [(originalRow_update A path hpath k i j hai hne hj).2]
    by_cases hold : i ∈ oldRows p path k.val
    · rw [hzero i hold, zero_sub, norm_neg, norm_mul]
      exact (mul_le_mul_of_nonneg_right (multiplier_bounds A path hpath k i hai).2
        (norm_nonneg _)).trans (by simpa only [one_mul] using hn _ hpivot)
    · have hpo : pivotLabel path k ∈ oldRows p path k.val := by
        by_contra hpn
        exact hne (front_new_unique p k.val path i hif hold
          (pivotLabel path k) hpivot hpn)
      rw [hzero _ hpo, mul_zero, sub_zero]
      exact hn i hif
  have hc : S.card ≤ p := (Finset.card_le_card hS).trans
    (front_invariant p q A hA path hpath (k.val + 1) (Nat.succ_le_of_lt k.isLt)).1
  rw [envelopeSum_time_one p S.card hc]
  simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum hnew

#print axioms old_column_advance_positive
#assert_trust kernel old_column_advance_positive
#print axioms old_column_advance_zero
#assert_trust kernel old_column_advance_zero

end NLA.IE13
