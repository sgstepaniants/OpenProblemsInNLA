/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

The zero-lower-band endpoint is attained by the identity with its literal
no-swap pivot path, in the original minimum admissible dimension.
-/
import NLA.IE13.TailAlgebra
import NLA.IE13.UpperBound

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.IE13

lemma origin_identity {n : ℕ} (k : ℕ) :
    origin (fun i : Fin n => i) k = Equiv.refl (Fin n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [origin]
    split_ifs with hk
    · rw [ih, Equiv.swap_self, Equiv.refl_trans]
    · exact ih

lemma identity_banded {n : ℕ} (p q : ℕ) : Banded p q (1 : Mat n) := by
  intro i j hband
  have hne : i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    rcases hband with h | h <;> omega
  exact Matrix.one_apply_ne hne

lemma identity_path_admissible {n : ℕ} :
    AdmissiblePath (1 : Mat n) (fun k => k) := by
  have hL : (1 : Mat n).IsLowerTriangular := by
    intro i j hij
    change i < j at hij
    exact Matrix.one_apply_ne (ne_of_lt hij)
  have hU : (1 : Mat n).IsUpperTriangular := by
    intro i j hji
    change j < i at hji
    exact Matrix.one_apply_ne (ne_of_gt hji)
  have hprefix := relabeled_LU_prefix_admissible
    (1 : Mat n) (1 : Mat n) (1 : Mat n) id (fun k => k) n
    (by intro i j; simp only [Matrix.one_mul, id_eq])
    hL (by intro i; exact Matrix.one_apply_eq i)
    hU (fun _ => le_rfl)
    (by intro k hk; rw [Matrix.one_apply_eq]; exact one_ne_zero)
    (by intro k hk; simp only [origin_identity, Equiv.refl_apply, id_eq])
    (by
      intro k hk i
      by_cases he : i = k
      · subst i
        simp only [Matrix.one_apply_eq, norm_one, le_refl]
      · rw [Matrix.one_apply_ne he, norm_zero]
        norm_num)
  intro k
  exact hprefix k k.isLt

theorem identity_attainment (q : ℕ) :
    BandedInput 0 q (1 : Mat (q + 1)) ∧
    AdmissiblePath (1 : Mat (q + 1)) (fun k => k) ∧
    growth (1 : Mat (q + 1)) (fun k => k) = 1 := by
  have hinput : BandedInput 0 q (1 : Mat (q + 1)) := by
    refine ⟨?_, identity_banded 0 q⟩
    rw [Matrix.det_one]
    exact one_ne_zero
  have hpath := identity_path_admissible (n := q + 1)
  exact ⟨hinput, hpath, zero_lower_bandwidth (by omega) q _ hinput _ hpath⟩

#print axioms identity_attainment
#assert_trust kernel identity_attainment

end NLA.IE13
