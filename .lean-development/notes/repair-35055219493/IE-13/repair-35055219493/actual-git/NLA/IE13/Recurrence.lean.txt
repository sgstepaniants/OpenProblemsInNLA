/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

The exact natural recurrence, with every truncated initial window retained.
No numerical recurrence evaluation or bound on p or t is required.
-/
import NLA.IE13.Definitions
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.BigOperators.Fin
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators
namespace NLA.IE13

@[simp] lemma bandSequence_zero (p : ℕ) : bandSequence p 0 = 0 := rfl

theorem recurrence_history (p t r : ℕ) :
    recurrenceHistory p t r = bandSequence p (t - r) := by
  induction t generalizing r with
  | zero => simp [recurrenceHistory, bandSequence]
  | succ t ih =>
    cases r with
    | zero => rfl
    | succ r =>
      simpa only [recurrenceHistory, Nat.succ_ne_zero, if_false,
        Nat.add_sub_cancel_right, Nat.add_sub_add_right] using ih r

theorem sequence_recurrence (p : ℕ) :
    bandSequence p 0 = 0 ∧
    ∀ t : ℕ, bandSequence p (t + 1) =
      1 + ∑ r : Fin p, bandSequence p (t - r.val) := by
  refine ⟨rfl, ?_⟩
  intro t
  change 1 + ∑ r : Fin p, recurrenceHistory p t r.val =
    1 + ∑ r : Fin p, bandSequence p (t - r.val)
  congr 1
  exact Finset.sum_congr rfl (fun r _ => recurrence_history p t r.val)

lemma sequence_recurrence_range (p t : ℕ) :
    bandSequence p (t + 1) =
      1 + ∑ r ∈ Finset.range p, bandSequence p (t - r) := by
  rw [(sequence_recurrence p).2 t,
    ← Finset.sum_range (fun r : ℕ => bandSequence p (t - r))]

lemma sequence_step_le (p t : ℕ) : bandSequence p t ≤ bandSequence p (t + 1) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    cases t with
    | zero => simp only [bandSequence_zero]; exact Nat.zero_le _
    | succ s =>
      rw [(sequence_recurrence p).2 s, (sequence_recurrence p).2 (s + 1)]
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro r _
      by_cases hr : r.val ≤ s
      · have he : s + 1 - r.val = (s - r.val) + 1 := by omega
        rw [he]
        exact ih (s - r.val) (by omega)
      · have he : s - r.val = 0 := by omega
        rw [he, bandSequence_zero]
        exact Nat.zero_le _

theorem sequence_properties (p : ℕ) :
    Monotone (bandSequence p) ∧
    ∀ t : ℕ, 0 < t → 0 < bandSequence p t := by
  refine ⟨monotone_nat_of_le_succ (sequence_step_le p), ?_⟩
  intro t ht
  cases t with
  | zero => omega
  | succ s =>
    rw [(sequence_recurrence p).2 s]
    omega

lemma sequence_ge_one (p t : ℕ) (ht : 0 < t) : 1 ≤ bandSequence p t :=
  (sequence_properties p).2 t ht

#print axioms recurrence_history
#assert_trust kernel recurrence_history
#print axioms sequence_recurrence
#assert_trust kernel sequence_recurrence
#print axioms sequence_properties
#assert_trust kernel sequence_properties

end NLA.IE13
