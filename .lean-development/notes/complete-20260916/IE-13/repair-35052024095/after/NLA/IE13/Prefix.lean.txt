/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

Complete any genuine GEPP prefix by selecting actual maximum-modulus pivots
after its end. Earlier pivot choices and every earlier state are preserved;
the unused suffix of the supplied path is never assumed admissible.
-/
import NLA.IE13.GEPP

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators NNReal
namespace NLA.IE13

lemma trajectory_agree_before {n : ℕ} (A : Mat n) (left right : PivotPath n)
    (s : ℕ) (h : ∀ k : Fin n, k.val < s → left k = right k) :
    trajectory A left s = trajectory A right s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have he : trajectory A left s = trajectory A right s :=
      ih (fun k hk => h k (by omega))
    by_cases hs : s < n
    · rw [trajectory, dif_pos hs, trajectory, dif_pos hs, he,
        h ⟨s, hs⟩ (Nat.lt_succ_self s)]
    · simp only [trajectory, dif_neg hs]

/-- Literal mixed trajectory; before t it uses exactly the user's supplied pivots. -/
def completionTrajectory {n : ℕ} (A : Mat n) (path : PivotPath n) (t : ℕ) : ℕ → Mat n
  | 0 => A
  | k + 1 => if h : k < n then
      schurStep (completionTrajectory A path t k) ⟨k, h⟩
        (if k < t then path ⟨k, h⟩ else maxPivot (completionTrajectory A path t k) ⟨k, h⟩)
    else 0

def completedPath {n : ℕ} (A : Mat n) (path : PivotPath n) (t : ℕ) : PivotPath n :=
  fun k => if k.val < t then path k else maxPivot (completionTrajectory A path t k.val) k

lemma trajectory_completedPath {n : ℕ} (A : Mat n) (path : PivotPath n) (t s : ℕ) :
    trajectory A (completedPath A path t) s = completionTrajectory A path t s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [trajectory, completionTrajectory, completedPath, ih]

lemma completedPath_agrees {n : ℕ} (A : Mat n) (path : PivotPath n) (t : ℕ)
    (k : Fin n) (hk : k.val < t) : completedPath A path t k = path k := by
  simp only [completedPath, if_pos hk]

lemma completedPath_prefix_states {n : ℕ} (A : Mat n) (path : PivotPath n)
    (t s : ℕ) (hs : s ≤ t) :
    trajectory A (completedPath A path t) s = trajectory A path s :=
  trajectory_agree_before A _ _ s
    (fun k hk => completedPath_agrees A path t k (lt_of_lt_of_le hk hs))

lemma completionTrajectory_prefix {n : ℕ} (A : Mat n) (path : PivotPath n)
    (t s : ℕ) (hs : s ≤ t) :
    completionTrajectory A path t s = trajectory A path s := by
  rw [← trajectory_completedPath]
  exact completedPath_prefix_states A path t s hs

lemma completionTrajectory_activeInjective {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    (path : PivotPath n) (t : ℕ) (hprefix : AdmissiblePrefix A path t)
    (s : ℕ) (hs : s ≤ n) : ActiveInjective (completionTrajectory A path t s) s := by
  induction s with
  | zero => exact activeInjective_initial A hA
  | succ s ih =>
    have hsn : s < n := by omega
    have hS := ih (by omega)
    have hp : AdmissiblePivot (completionTrajectory A path t s) ⟨s, hsn⟩
        (if s < t then path ⟨s, hsn⟩ else
          maxPivot (completionTrajectory A path t s) ⟨s, hsn⟩) := by
      by_cases hst : s < t
      · rw [if_pos hst, completionTrajectory_prefix A path t s hst.le]
        exact hprefix ⟨s, hsn⟩ hst
      · rw [if_neg hst]
        exact maxPivot_admissible _ _ hS
    simpa only [completionTrajectory, dif_pos hsn] using
      activeInjective_schur (completionTrajectory A path t s) ⟨s, hsn⟩ _
        hp.1 hp.2.1 hS

lemma completedPath_admissible {n : ℕ} (A : Mat n) (hA : A.det ≠ 0)
    (path : PivotPath n) (t : ℕ) (hprefix : AdmissiblePrefix A path t) :
    AdmissiblePath A (completedPath A path t) := by
  intro k
  rw [trajectory_completedPath]
  by_cases hk : k.val < t
  · rw [completedPath_agrees A path t k hk,
      completionTrajectory_prefix A path t k.val hk.le]
    exact hprefix k hk
  · simp only [completedPath, if_neg hk]
    exact maxPivot_admissible _ k
      (completionTrajectory_activeInjective A hA path t hprefix k.val k.isLt.le)

theorem admissiblePrefix_extension {n : ℕ} (hn : 1 ≤ n) (A : Mat n)
    (hA : A.det ≠ 0) (path : PivotPath n) (t : ℕ) (ht : t ≤ n)
    (hprefix : AdmissiblePrefix A path t) :
    ∃ full : PivotPath n, AdmissiblePath A full ∧
      (∀ k : Fin n, k.val < t → full k = path k) ∧
      ∀ s : ℕ, s ≤ t → trajectory A full s = trajectory A path s := by
  refine ⟨completedPath A path t, completedPath_admissible A hA path t hprefix, ?_, ?_⟩
  · exact fun k hk => completedPath_agrees A path t k hk
  · exact fun s hs => completedPath_prefix_states A path t s hs

#print axioms trajectory_agree_before
#assert_trust kernel trajectory_agree_before
#print axioms admissiblePrefix_extension
#assert_trust kernel admissiblePrefix_extension

end NLA.IE13
