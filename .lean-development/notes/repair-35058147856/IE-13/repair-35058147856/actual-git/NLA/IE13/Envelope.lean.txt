/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

Exact sorted envelope and finite partial sums. The appended unit bound is
scalar bookkeeping only; no artificial row is added to the actual algorithm.
-/
import NLA.IE13.Recurrence
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators
namespace NLA.IE13

@[simp] lemma envelope_zero (p : ℕ) (i : Fin p) : envelope p 0 i = 0 := by
  simp only [envelope, if_true]

@[simp] lemma envelope_one (p : ℕ) (i : Fin p) : envelope p 1 i = 1 := by
  rw [envelope, if_neg (by omega : (1 : ℕ) ≠ 0)]
  have hzero (r : ℕ) : 1 - (r + 1) = 0 := by omega
  simp only [hzero, bandSequence_zero, Finset.sum_const_zero, Nat.add_zero]

lemma envelope_first (p t : ℕ) (hp : 0 < p) (ht : 1 ≤ t) :
    envelope p t ⟨0, hp⟩ = bandSequence p t := by
  cases t with
  | zero => omega
  | succ s =>
    rw [envelope, if_neg (by omega : s + 1 ≠ 0)]
    change 1 + ∑ r ∈ Finset.range p, bandSequence p (s + 1 - (r + 1)) =
      bandSequence p (s + 1)
    rw [sequence_recurrence_range p s]
    congr 1
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    omega

lemma envelope_ge_one (p t : ℕ) (ht : 1 ≤ t) (i : Fin p) :
    1 ≤ envelope p t i := by
  rw [envelope, if_neg (by omega : t ≠ 0)]
  omega

lemma envelope_antitone (p t : ℕ) : Antitone (envelope p t) := by
  intro i j hij
  by_cases ht : t = 0
  · simp only [ht, envelope_zero, le_refl]
  · simp only [envelope, if_neg ht]
    apply Nat.add_le_add_left
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.range_mono
      have hv : i.val ≤ j.val := hij
      omega
    · intro r _ _
      exact Nat.zero_le _

lemma envelope_step (p t : ℕ) (ht : 1 ≤ t) (i : Fin p) :
    envelope p (t + 1) i = bandSequence p t +
      (if h : i.val + 1 < p then envelope p t ⟨i.val + 1, h⟩ else 1) := by
  rw [envelope, if_neg (by omega : t + 1 ≠ 0)]
  have hsum :
      (∑ r ∈ Finset.range (p - i.val), bandSequence p (t + 1 - (r + 1))) =
        ∑ r ∈ Finset.range (p - i.val), bandSequence p (t - r) := by
    apply Finset.sum_congr rfl
    intro r _
    congr 1
    omega
  rw [hsum]
  by_cases hi : i.val + 1 < p
  · rw [dif_pos hi]
    have hlen : p - i.val = (p - (i.val + 1)) + 1 := by omega
    rw [hlen, Finset.sum_range_succ', envelope, if_neg (by omega : t ≠ 0)]
    simp only [Nat.sub_zero]
    omega
  · rw [dif_neg hi]
    have hlen : p - i.val = 1 := by have his := i.isLt; omega
    rw [hlen, Finset.sum_range_one]
    simp only [Nat.sub_zero]
    omega

theorem envelope_recurrence (p : ℕ) (hp : 0 < p) :
    (∀ i : Fin p, envelope p 0 i = 0 ∧ envelope p 1 i = 1) ∧
    ∀ t : ℕ, 1 ≤ t →
      envelope p t ⟨0, hp⟩ = bandSequence p t ∧
      (∀ i : Fin p, 1 ≤ envelope p t i) ∧
      (∀ i j : Fin p, i ≤ j → envelope p t j ≤ envelope p t i) ∧
      ∀ i : Fin p, envelope p (t + 1) i = bandSequence p t +
        (if h : i.val + 1 < p then envelope p t ⟨i.val + 1, h⟩ else 1) := by
  refine ⟨fun i => ⟨envelope_zero p i, envelope_one p i⟩, ?_⟩
  intro t ht
  exact ⟨envelope_first p t hp ht, envelope_ge_one p t ht,
    envelope_antitone p t, envelope_step p t ht⟩

@[simp] lemma envelopeSum_zero (p t : ℕ) : envelopeSum p t 0 = 0 := by
  simp [envelopeSum]

@[simp] lemma envelopeSum_initial (p r : ℕ) : envelopeSum p 0 r = 0 := by
  simp [envelopeSum]

lemma envelopeSum_succ (p t r : ℕ) (hr : r < p) :
    envelopeSum p t (r + 1) = envelopeSum p t r + envelope p t ⟨r, hr⟩ := by
  classical
  let a : Fin p := ⟨r, hr⟩
  have hterm (i : Fin p) :
      (if i.val < r + 1 then envelope p t i else 0) =
        (if i.val < r then envelope p t i else 0) +
          (if i = a then envelope p t a else 0) := by
    by_cases hi : i = a
    · subst i
      simp [a]
    · have hne : i.val ≠ r := fun h => hi (Fin.ext h)
      by_cases hlt : i.val < r
      · have hlt' : i.val < r + 1 := by omega
        simp only [if_pos hlt, if_pos hlt', if_neg hi, Nat.add_zero]
      · have hlt' : ¬i.val < r + 1 := by omega
        simp only [if_neg hlt, if_neg hlt', if_neg hi, Nat.add_zero]
  unfold envelopeSum
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
  simp [a]

lemma envelopeSum_monotone (p t : ℕ) : Monotone (envelopeSum p t) := by
  intro r s hrs
  unfold envelopeSum
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val < r
  · have his : i.val < s := lt_of_lt_of_le hi hrs
    simp only [if_pos hi, if_pos his, le_refl]
  · simp only [if_neg hi]
    exact Nat.zero_le _

lemma envelopeSum_one (p t : ℕ) (hp : 0 < p) (ht : 1 ≤ t) :
    envelopeSum p t 1 = bandSequence p t := by
  change envelopeSum p t (0 + 1) = bandSequence p t
  rw [envelopeSum_succ p t 0 hp,
    envelopeSum_zero, Nat.zero_add, envelope_first p t hp ht]

/-- A subtraction-free form of both partial-sum recurrences used by the subset bound. -/
lemma envelopeSum_step (p t r : ℕ) (hp : 0 < p) (ht : 1 ≤ t) (hr : r ≤ p) :
    envelopeSum p (t + 1) r + bandSequence p t =
      envelopeSum p t r +
        (if h : r < p then envelope p t ⟨r, h⟩ else 1) + r * bandSequence p t := by
  revert hr
  induction r with
  | zero =>
    intro hr
    rw [envelopeSum_zero, envelopeSum_zero, dif_pos hp,
      envelope_first p t hp ht]
    simp
  | succ r ih =>
    intro hr
    have hrp : r < p := by omega
    have hprev := ih hrp.le
    rw [dif_pos hrp] at hprev
    rw [envelopeSum_succ p (t + 1) r hrp, envelopeSum_succ p t r hrp,
      envelope_step p t ht ⟨r, hrp⟩]
    simp only [Fin.val_mk, Nat.succ_mul]
    omega

#print axioms envelope_recurrence
#assert_trust kernel envelope_recurrence
#print axioms envelopeSum_step
#assert_trust kernel envelopeSum_step

end NLA.IE13
