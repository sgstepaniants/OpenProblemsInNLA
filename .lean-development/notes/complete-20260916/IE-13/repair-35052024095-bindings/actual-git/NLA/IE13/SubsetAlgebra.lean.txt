/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

Finite-subset inequalities behind the general-band estimate. Appending at most
one entry and deleting the actual pivot never requires sorting or enumerating
subsets in the evaluator. These are symbolic all-cardinality estimates.
-/
import NLA.IE13.Envelope

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators
namespace NLA.IE13

lemma erase_new_subset_old {ι : Type*} [DecidableEq ι] (O F S : Finset ι) (a : ι)
    (hS : S ⊆ F) (ha : a ∈ S) (haO : a ∉ O)
    (hunique : ∀ i ∈ F, i ∉ O → ∀ j ∈ F, j ∉ O → i = j) :
    S.erase a ⊆ O := by
  intro i hi
  obtain ⟨hia, hiS⟩ := Finset.mem_erase.mp hi
  by_contra hiO
  exact hia (hunique i (hS hiS) hiO a (hS ha) haO)

lemma one_new_small_subset {ι : Type*} [DecidableEq ι]
    (p t : ℕ) (ht : 1 ≤ t) (O F : Finset ι) (v : ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hunique : ∀ i ∈ F, i ∉ O → ∀ j ∈ F, j ∉ O → i = j)
    (hnew : ∀ i ∈ F, i ∉ O → v i ≤ M)
    (hbound : ∀ S : Finset ι, S ⊆ O →
      (∑ i ∈ S, v i) ≤ (envelopeSum p t S.card : ℝ) * M)
    (S : Finset ι) (hS : S ⊆ F) (hcard : S.card ≤ p) :
    (∑ i ∈ S, v i) ≤ (envelopeSum p t S.card : ℝ) * M := by
  by_cases hSO : S ⊆ O
  · exact hbound S hSO
  · obtain ⟨a, ha, haO⟩ := Finset.not_subset.mp hSO
    have he := erase_new_subset_old O F S a hS ha haO hunique
    have hb := hbound (S.erase a) he
    have haM := hnew a (hS ha) haO
    have hc := Finset.card_erase_add_one ha
    have hr : (S.erase a).card < p := by omega
    have hstep : envelopeSum p t (S.erase a).card + 1 ≤ envelopeSum p t S.card := by
      rw [← hc, envelopeSum_succ p t (S.erase a).card hr]
      exact Nat.add_le_add_left (envelope_ge_one p t ht ⟨(S.erase a).card, hr⟩) _
    calc
      (∑ i ∈ S, v i) = (∑ i ∈ S.erase a, v i) + v a :=
        (Finset.sum_erase_add S v ha).symm
      _ ≤ (envelopeSum p t (S.erase a).card : ℝ) * M + M := add_le_add hb haM
      _ = ((envelopeSum p t (S.erase a).card + 1 : ℕ) : ℝ) * M := by
        push_cast
        ring
      _ ≤ (envelopeSum p t S.card : ℝ) * M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hstep) hM

lemma one_new_full_subset {ι : Type*} [DecidableEq ι]
    (p t : ℕ) (O F : Finset ι) (hO : O.card ≤ p) (v : ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M)
    (hunique : ∀ i ∈ F, i ∉ O → ∀ j ∈ F, j ∉ O → i = j)
    (hnew : ∀ i ∈ F, i ∉ O → v i ≤ M)
    (hbound : ∀ S : Finset ι, S ⊆ O →
      (∑ i ∈ S, v i) ≤ (envelopeSum p t S.card : ℝ) * M)
    (S : Finset ι) (hS : S ⊆ F) :
    (∑ i ∈ S, v i) ≤ ((envelopeSum p t p + 1 : ℕ) : ℝ) * M := by
  have hpartial : ∀ U : Finset ι, U ⊆ O →
      (∑ i ∈ U, v i) ≤ (envelopeSum p t p : ℝ) * M := by
    intro U hU
    have hc := (Finset.card_le_card hU).trans hO
    exact (hbound U hU).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast envelopeSum_monotone p t hc) hM)
  by_cases hSO : S ⊆ O
  · calc
      (∑ i ∈ S, v i) ≤ (envelopeSum p t p : ℝ) * M := hpartial S hSO
      _ ≤ ((envelopeSum p t p + 1 : ℕ) : ℝ) * M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ (envelopeSum p t p)) hM
  · obtain ⟨a, ha, haO⟩ := Finset.not_subset.mp hSO
    have he := erase_new_subset_old O F S a hS ha haO hunique
    calc
      (∑ i ∈ S, v i) = (∑ i ∈ S.erase a, v i) + v a :=
        (Finset.sum_erase_add S v ha).symm
      _ ≤ (envelopeSum p t p : ℝ) * M + M :=
        add_le_add (hpartial (S.erase a) he) (hnew a (hS ha) haO)
      _ = ((envelopeSum p t p + 1 : ℕ) : ℝ) * M := by push_cast; ring

/-- One complex elimination update, simultaneously for every surviving subset. -/
lemma subset_update_bound {ι : Type*} [DecidableEq ι]
    (p t : ℕ) (hp : 0 < p) (ht : 1 ≤ t) (F : Finset ι) (a : ι) (ha : a ∈ F)
    (v μ : ι → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hsmall : ∀ S : Finset ι, S ⊆ F → S.card ≤ p →
      (∑ i ∈ S, ‖v i‖) ≤ (envelopeSum p t S.card : ℝ) * M)
    (hfull : ∀ S : Finset ι, S ⊆ F →
      (∑ i ∈ S, ‖v i‖) ≤ ((envelopeSum p t p + 1 : ℕ) : ℝ) * M)
    (S : Finset ι) (hS : S ⊆ F.erase a) (hcard : S.card ≤ p)
    (hμ : ∀ i ∈ S, ‖μ i‖ ≤ 1) :
    (∑ i ∈ S, ‖v i - μ i * v a‖) ≤ (envelopeSum p (t + 1) S.card : ℝ) * M := by
  by_cases hzero : S = ∅
  · subst S
    simp
  have hpos : 1 ≤ S.card := by
    have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hzero)
    omega
  have haS : a ∉ S := by
    intro h
    exact Finset.notMem_erase a F (hS h)
  have hSF : S ⊆ F := fun i hi => (Finset.mem_erase.mp (hS hi)).2
  have hUF : insert a S ⊆ F := by
    intro i hi
    rcases Finset.mem_insert.mp hi with hia | hiS
    · simpa only [hia] using ha
    · exact hSF hiS
  have hsingleton := hsmall {a} (by simpa using ha)
    (by simp only [Finset.card_singleton]; omega)
  have hpivot : ‖v a‖ ≤ (bandSequence p t : ℝ) * M := by
    simpa only [Finset.sum_singleton, Finset.card_singleton,
      envelopeSum_one p t hp ht] using hsingleton
  have hunion : (∑ i ∈ insert a S, ‖v i‖) ≤
      ((envelopeSum p t S.card +
        (if h : S.card < p then envelope p t ⟨S.card, h⟩ else 1) : ℕ) : ℝ) * M := by
    by_cases hr : S.card < p
    · have hu := hsmall (insert a S) hUF (by rw [Finset.card_insert_of_notMem haS]; omega)
      simpa only [Finset.card_insert_of_notMem haS, envelopeSum_succ p t S.card hr,
        dif_pos hr] using hu
    · have he : S.card = p := by omega
      simpa only [he, dif_neg (Nat.lt_irrefl p)] using hfull (insert a S) hUF
  have hnorm (i : ι) (hi : i ∈ S) : ‖v i - μ i * v a‖ ≤ ‖v i‖ + ‖v a‖ := by
    calc
      ‖v i - μ i * v a‖ ≤ ‖v i‖ + ‖μ i * v a‖ := norm_sub_le _ _
      _ = ‖v i‖ + ‖μ i‖ * ‖v a‖ := by rw [norm_mul]
      _ ≤ ‖v i‖ + ‖v a‖ := by
        have := mul_le_mul_of_nonneg_right (hμ i hi) (norm_nonneg (v a))
        simpa only [one_mul] using add_le_add (le_refl ‖v i‖) this
  have hs := Finset.sum_le_sum hnorm
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_const, nsmul_eq_mul] at hs
  have hsum : (∑ i ∈ insert a S, ‖v i‖) = ‖v a‖ + ∑ i ∈ S, ‖v i‖ :=
    Finset.sum_insert haS
  have hc : ((S.card - 1 : ℕ) : ℝ) + 1 = (S.card : ℝ) := by
    exact_mod_cast (show S.card - 1 + 1 = S.card by omega)
  have hupdate : (∑ i ∈ S, ‖v i - μ i * v a‖) ≤
      (∑ i ∈ insert a S, ‖v i‖) + ((S.card - 1 : ℕ) : ℝ) * ‖v a‖ := by
    rw [hsum]
    rw [← hc] at hs
    nlinarith only [hs]
  have hcoef := envelopeSum_step p t S.card hp ht hcard
  have hcoefR : (envelopeSum p (t + 1) S.card : ℝ) + (bandSequence p t : ℝ) =
      (envelopeSum p t S.card : ℝ) +
        ((if h : S.card < p then envelope p t ⟨S.card, h⟩ else 1 : ℕ) : ℝ) +
        (S.card : ℝ) * (bandSequence p t : ℝ) := by exact_mod_cast hcoef
  have hpivot' := mul_le_mul_of_nonneg_left hpivot
    (Nat.cast_nonneg (S.card - 1) : (0 : ℝ) ≤ ((S.card - 1 : ℕ) : ℝ))
  have hfinal := add_le_add hunion hpivot'
  simp only [Nat.cast_add] at hfinal
  have hcoefM := congrArg (fun z : ℝ => z * M) hcoefR
  have hcardM := congrArg (fun z : ℝ => z * (bandSequence p t : ℝ) * M) hc
  nlinarith only [hupdate, hfinal, hcoefM, hcardM]

#print axioms subset_update_bound
#assert_trust kernel subset_update_bound

end NLA.IE13
