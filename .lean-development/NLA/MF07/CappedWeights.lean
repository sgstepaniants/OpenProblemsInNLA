/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original capped singular-gap argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

A constructive induction caps each adjacent singular-value ratio by s. Equal
ratios of the old and new weights form full blocks; a strict block separation
forces an s-sized gap in both coordinate systems. No interval grid is used.
-/
import NLA.MF07.BlockComparison

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF07

lemma antitone_fin_prepend {n : ℕ} (f : Fin (n + 1) → ℝ) (a : ℝ)
    (hf : Antitone f) (ha : f 0 ≤ a) : Antitone (Fin.cases a f) := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => exact le_rfl
      | succ j => exact (hf (Fin.zero_le j)).trans ha
  | succ i =>
      cases j using Fin.cases with
      | zero => exact False.elim (by simpa using hij)
      | succ j => exact hf (by simpa using hij)

lemma exists_capped_weights_succ (n : ℕ) :
    ∀ (σ : Fin (n + 1) → ℝ), Antitone σ → (∀ i, 0 < σ i) →
    ∀ (s : ℝ), 1 ≤ s →
    ∃ τ : Fin (n + 1) → ℝ,
      (∀ i, 1 ≤ τ i ∧ τ i ≤ s ^ n) ∧ Antitone τ ∧
      Antitone (fun i => σ i / τ i) ∧
      ∀ i j, σ j / τ j < σ i / τ i →
        s * σ j ≤ σ i ∧ s * τ j ≤ τ i := by
  induction n with
  | zero =>
      intro σ hmono hpos s hs
      refine ⟨fun _ => 1, ?_, ?_, ?_, ?_⟩
      · intro i
        simp
      · intro i j hij
        exact le_rfl
      · simpa only [div_one] using hmono
      · intro i j hij
        have he : i = j := Subsingleton.elim _ _
        subst j
        exact False.elim (lt_irrefl _ hij)
  | succ n ih =>
      intro σ hmono hpos s hs
      let σt : Fin (n + 1) → ℝ := fun i => σ i.succ
      have htm : Antitone σt := by
        intro i j hij
        exact hmono (by simpa using hij)
      obtain ⟨t, ht, htm', hhm', hwide⟩ := ih σt htm (fun i => hpos i.succ) s hs
      let ρ : ℝ := σ 0 / σ (Fin.succ 0)
      let θ : ℝ := min ρ s
      let τ : Fin (n + 1 + 1) → ℝ := Fin.cases (θ * t 0) t
      have htpos : ∀ i, 0 < t i := fun i => lt_of_lt_of_le zero_lt_one (ht i).1
      have hσ01 : σ (Fin.succ 0) ≤ σ 0 := hmono (Fin.zero_le _)
      have hρ : 1 ≤ ρ := (le_div_iff₀ (hpos (Fin.succ 0))).2 (by simpa using hσ01)
      have hθ : 1 ≤ θ := le_min hρ hs
      have hθpos : 0 < θ := lt_of_lt_of_le zero_lt_one hθ
      have hθs : θ ≤ s := min_le_right _ _
      have hθσ : θ * σ (Fin.succ 0) ≤ σ 0 :=
        (le_div_iff₀ (hpos (Fin.succ 0))).mp (min_le_left ρ s)
      have hhead : σ (Fin.succ 0) / t 0 ≤ σ 0 / (θ * t 0) := by
        apply (div_le_div_iff₀ (htpos 0) (mul_pos hθpos (htpos 0))).mpr
        calc
          σ (Fin.succ 0) * (θ * t 0) = (θ * σ (Fin.succ 0)) * t 0 := by ring
          _ ≤ σ 0 * t 0 := mul_le_mul_of_nonneg_right hθσ (htpos 0).le
      have hτm : Antitone τ := by
        apply antitone_fin_prepend t (θ * t 0) htm'
        nlinarith [htpos 0]
      have hhfun : (fun i => σ i / τ i) =
          Fin.cases (σ 0 / (θ * t 0)) (fun i => σt i / t i) := by
        funext i
        cases i using Fin.cases <;> rfl
      have hhm : Antitone (fun i => σ i / τ i) := by
        rw [hhfun]
        exact antitone_fin_prepend _ _ hhm' hhead
      refine ⟨τ, ?_, hτm, hhm, ?_⟩
      · intro i
        cases i using Fin.cases with
        | zero =>
            change 1 ≤ θ * t 0 ∧ θ * t 0 ≤ s ^ (n + 1)
            constructor
            · nlinarith [(ht 0).1]
            · calc
                θ * t 0 ≤ s * s ^ n :=
                  mul_le_mul hθs (ht 0).2 (htpos 0).le (lt_of_lt_of_le zero_lt_one hs).le
                _ = s ^ (n + 1) := (pow_succ' s n).symm
        | succ i =>
            change 1 ≤ t i ∧ t i ≤ s ^ (n + 1)
            refine ⟨(ht i).1, (ht i).2.trans ?_⟩
            calc
              s ^ n = s ^ n * 1 := (mul_one _).symm
              _ ≤ s ^ n * s := mul_le_mul_of_nonneg_left hs (pow_nonneg (by linarith) _)
              _ = s ^ (n + 1) := (pow_succ s n).symm
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
            cases j using Fin.cases with
            | zero => exact False.elim (lt_irrefl _ hij)
            | succ j =>
                change σt j / t j < σ 0 / (θ * t 0) at hij
                change s * σt j ≤ σ 0 ∧ s * t j ≤ θ * t 0
                by_cases hρs : ρ ≤ s
                · have he : σ 0 / (θ * t 0) = σt 0 / t 0 := by
                    dsimp [θ]
                    rw [min_eq_left hρs]
                    dsimp [ρ, σt]
                    field_simp [(hpos 0).ne', (hpos (Fin.succ 0)).ne', (htpos 0).ne'] <;> ring
                  rw [he] at hij
                  obtain ⟨hσj, htj⟩ := hwide 0 j hij
                  constructor
                  · exact hσj.trans hσ01
                  · exact htj.trans (by nlinarith [htpos 0])
                · have he : θ = s := min_eq_right (le_of_not_ge hρs)
                  constructor
                  · calc
                      s * σt j ≤ s * σt 0 :=
                        mul_le_mul_of_nonneg_left (htm (Fin.zero_le j)) (by linarith)
                      _ ≤ σ 0 := by simpa only [σt, he] using hθσ
                  · rw [he]
                    exact mul_le_mul_of_nonneg_left (htm' (Fin.zero_le j)) (by linarith)
        | succ i =>
            cases j using Fin.cases with
            | zero =>
                exact False.elim (not_lt_of_ge (hhm (Fin.zero_le i.succ)) hij)
            | succ j => exact hwide i j hij

lemma exists_capped_weights {d : ℕ} (hd : 1 ≤ d) (σ : Fin d → ℝ)
    (hmono : Antitone σ) (hpos : ∀ i, 0 < σ i) (s : ℝ) (hs : 1 ≤ s) :
    ∃ τ : Fin d → ℝ,
      (∀ i, 1 ≤ τ i ∧ τ i ≤ s ^ (d - 1)) ∧ Antitone τ ∧
      Antitone (fun i => σ i / τ i) ∧
      ∀ i j, σ j / τ j < σ i / τ i →
        s * σ j ≤ σ i ∧ s * τ j ≤ τ i := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  simpa using exists_capped_weights_succ n σ hmono hpos s hs

lemma divided_weight_entry_bound {L s a b : ℝ} (hL : 0 ≤ L) (hs : 0 < s)
    (ha : 0 < a) (hwide : s * b ≤ a) : L * b / a ≤ L / s := by
  have hratio : b / a ≤ 1 / s := (div_le_div_iff₀ ha hs).mpr (by nlinarith)
  simpa only [mul_div_assoc, mul_one] using mul_le_mul_of_nonneg_left hratio hL

#print axioms exists_capped_weights
#assert_trust kernel exists_capped_weights

end NLA.MF07
