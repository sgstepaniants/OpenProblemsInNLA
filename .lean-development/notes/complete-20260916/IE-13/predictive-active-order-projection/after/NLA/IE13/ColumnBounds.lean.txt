/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

Full finite-subset estimate for every actual old-row front and target column.
Early columns start at age one; late columns retain their exact zero phase.
-/
import NLA.IE13.FrontBounds

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators
namespace NLA.IE13

lemma columnAge_zero_iff {n : ℕ} (p q k : ℕ) (j : Fin n) :
    columnAge p q k j = 0 ↔ k + p + q ≤ j.val := by
  unfold columnAge
  split_ifs <;> omega

lemma columnAge_succ_of_pos {n : ℕ} (p q k : ℕ) (j : Fin n)
    (hpos : 0 < columnAge p q k j) :
    columnAge p q (k + 1) j = columnAge p q k j + 1 := by
  by_cases hj : j.val < p + q
  · simp only [columnAge, if_pos hj]
  · simp only [columnAge, if_neg hj] at hpos ⊢
    omega

lemma columnAge_first {n : ℕ} (p q k : ℕ) (j : Fin n)
    (hzero : columnAge p q k j = 0) (hnew : ¬ k + 1 + p + q ≤ j.val) :
    columnAge p q (k + 1) j = 1 := by
  have hprior := (columnAge_zero_iff p q k j).mp hzero
  have hj : ¬j.val < p + q := by omega
  simp only [columnAge, if_neg hj]
  omega

lemma columnAge_le_band {n : ℕ} (p q k : ℕ) (j : Fin n) (hkj : k ≤ j.val) :
    columnAge p q k j ≤ p + q := by
  unfold columnAge
  split_ifs <;> omega

lemma zero_column_subset_bound {n : ℕ} (p q k : ℕ)
    (A : Mat n) (hA : Banded p q A) (path : PivotPath n)
    (hpath : AdmissiblePath A path) (j : Fin n) (hlate : k + p + q ≤ j.val) :
    ∀ S : Finset (Fin n), S ⊆ oldRows p path k →
      (∑ i ∈ S, ‖originalRowStage A path k i j‖) ≤
        (envelopeSum p (columnAge p q k j) S.card : ℝ) * entryMax A := by
  intro S hS
  rw [(columnAge_zero_iff p q k j).mpr hlate, envelopeSum_initial, Nat.cast_zero, zero_mul]
  have hz := late_column_zero_at p q A hA path hpath k j hlate
  exact le_of_eq (Finset.sum_eq_zero (fun i hi => by rw [hz i (hS hi), norm_zero]))

lemma column_front_bound_at {n : ℕ} (p q : ℕ) (hp : 0 < p)
    (A : Mat n) (hA : Banded p q A) (path : PivotPath n)
    (hpath : AdmissiblePath A path) (k : ℕ) (j : Fin n) (hkj : k ≤ j.val) :
    ∀ S : Finset (Fin n), S ⊆ oldRows p path k →
      (∑ i ∈ S, ‖originalRowStage A path k i j‖) ≤
        (envelopeSum p (columnAge p q k j) S.card : ℝ) * entryMax A := by
  revert hkj
  induction k with
  | zero =>
    intro hkj
    by_cases hlate : 0 + p + q ≤ j.val
    · exact zero_column_subset_bound p q 0 A hA path hpath j hlate
    · intro S hS
      have hj : j.val < p + q := by omega
      have hc : S.card ≤ p := (Finset.card_le_card hS).trans (oldRows_initial_card p path)
      have hage : columnAge p q 0 j = 1 := by simp only [columnAge, if_pos hj]
      rw [hage, envelopeSum_time_one p S.card hc]
      change (∑ i ∈ S, ‖A i j‖) ≤ (S.card : ℝ) * entryMax A
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        (Finset.sum_le_sum (fun i (_hi : i ∈ S) => norm_le_entryMax A i j))
  | succ k ih =>
    intro hkj
    have hkn : k < n := by have hjn := j.isLt; omega
    let z : Fin n := ⟨k, hkn⟩
    have hj : z < j := by change k < j.val; omega
    by_cases hlate : k + 1 + p + q ≤ j.val
    · exact zero_column_subset_bound p q (k + 1) A hA path hpath j hlate
    · by_cases hzero : columnAge p q k j = 0
      · have hz := late_column_zero_at p q A hA path hpath k j
          ((columnAge_zero_iff p q k j).mp hzero)
        have hnext := old_column_advance_zero p q A hA path hpath z j hj hz
        simpa only [columnAge_first p q k j hzero hlate] using hnext
      · have ht : 1 ≤ columnAge p q k j := by omega
        have hprev := ih (by omega : k ≤ j.val)
        have hnext := old_column_advance_positive p q (columnAge p q k j) hp ht
          A hA path hpath z j hj hprev
        simpa only [columnAge_succ_of_pos p q k j (by omega)] using hnext

theorem column_front_bound {n : ℕ} (p q : ℕ) (hp : 0 < p)
    (A : Mat n) (hA : Banded p q A) (path : PivotPath n)
    (hpath : AdmissiblePath A path) (k j : Fin n) (hkj : k ≤ j) :
    ∀ S : Finset (Fin n), S ⊆ oldRows p path k.val →
      (∑ i ∈ S, ‖originalRowStage A path k.val i j‖) ≤
        (envelopeSum p (columnAge p q k.val j) S.card : ℝ) * entryMax A :=
  column_front_bound_at p q hp A hA path hpath k.val j hkj

#print axioms column_front_bound
#assert_trust kernel column_front_bound

end NLA.IE13
