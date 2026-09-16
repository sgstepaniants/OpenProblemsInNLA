/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

A dimension-independent entry bound follows from five fixed-size terms.
All spectral and eventual hypotheses are discharged in the final theorem,
including the exceptional positive parameter and every finite source index.
-/
import NLA.MF22.GreenCoefficients
import NLA.MF22.GreenEntryAlgebra
import NLA.MF22.SpectralTailBounds
import NLA.MF22.Roots

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22

noncomputable section

def greenEntryMajorant (C L P G τ : ℝ) : ℝ :=
  L * (4 * P * G) + 4 * C * G + τ * (P * (4 * C * G)) +
    τ * (C * (4 * P * G)) + τ * (C * (4 * C * G)) + 1

lemma greenEntryMajorant_pos (C L P G τ : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hP : 0 ≤ P) (hG : 0 ≤ G) (hτ : 0 ≤ τ) :
    0 < greenEntryMajorant C L P G τ := by
  unfold greenEntryMajorant
  positivity

lemma green_entry_bound_of_estimates (ρ : ℝ) (roots : Fin 4 → ℂ)
    (hsandwich : spectralProjector ρ roots 3 * boundaryOuter * spectralProjector ρ roots 3 =
      dominantGamma ρ roots • spectralProjector ρ roots 3)
    (C L P G τ : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hP : 0 ≤ P)
    (hG : 0 ≤ G) (hτ : 0 ≤ τ)
    (hProj : ∀ r s : Fin 4, ‖spectralProjector ρ roots 3 r s‖ ≤ P)
    (hRem : ∀ k : ℕ, ∀ r s : Fin 4, ‖spectralRemainder ρ roots k r s‖ ≤ C)
    (hForcing : ∀ r : Fin 4, ∀ s : Fin 2, ‖forcingMatrix ρ r s‖ ≤ G)
    (n j ell : ℕ)
    (hLeading : ‖greenLeadingCoefficient ρ roots n j ell‖ ≤ L)
    (hLeft : ‖(boundaryScalar ρ n)⁻¹ * roots 3 ^ j‖ ≤ τ)
    (hRight : ‖(boundaryScalar ρ n)⁻¹ * roots 3 ^ (n - 1 - ell)‖ ≤ τ)
    (hInv : ‖(boundaryScalar ρ n)⁻¹‖ ≤ τ) (r : Fin 4) (s : Fin 2) :
    ‖greenKernel ρ n j ell r s‖ ≤ greenEntryMajorant C L P G τ := by
  have h₁ : ‖greenLeadingCoefficient ρ roots n j ell *
      (spectralProjector ρ roots 3 * forcingMatrix ρ) r s‖ ≤ L * (4 * P * G) := by
    rw [norm_mul]
    exact mul_le_mul hLeading
      (norm_four_product_entry_bound _ _ P G hP hProj hForcing r s)
      (norm_nonneg _) hL
  have h₂ : ‖(if ell < j then
      spectralRemainder ρ roots (j - 1 - ell) * forcingMatrix ρ else 0) r s‖ ≤
      4 * C * G := by
    by_cases h : ell < j
    · rw [if_pos h]
      exact norm_four_product_entry_bound _ _ C G hC (hRem _) hForcing r s
    · simp only [if_neg h, Matrix.zero_apply, norm_zero]
      positivity
  have h₃ : ‖((boundaryScalar ρ n)⁻¹ * roots 3 ^ j) *
      (spectralProjector ρ roots 3 * boundaryOuter *
        spectralRemainder ρ roots (n - 1 - ell) * forcingMatrix ρ) r s‖ ≤
      τ * (P * (4 * C * G)) := by
    rw [norm_mul]
    exact mul_le_mul hLeft
      (norm_boundary_four_product_bound _ _ _ P C G hP hC hProj (hRem _) hForcing r s)
      (norm_nonneg _) hτ
  have h₄ : ‖((boundaryScalar ρ n)⁻¹ * roots 3 ^ (n - 1 - ell)) *
      (spectralRemainder ρ roots j * boundaryOuter *
        spectralProjector ρ roots 3 * forcingMatrix ρ) r s‖ ≤
      τ * (C * (4 * P * G)) := by
    rw [norm_mul]
    exact mul_le_mul hRight
      (norm_boundary_four_product_bound _ _ _ C P G hC hP (hRem _) hProj hForcing r s)
      (norm_nonneg _) hτ
  have h₅ : ‖(boundaryScalar ρ n)⁻¹ *
      (spectralRemainder ρ roots j * boundaryOuter *
        spectralRemainder ρ roots (n - 1 - ell) * forcingMatrix ρ) r s‖ ≤
      τ * (C * (4 * C * G)) := by
    rw [norm_mul]
    exact mul_le_mul hInv
      (norm_boundary_four_product_bound _ _ _ C C G hC hC (hRem _) (hRem _)
        hForcing r s) (norm_nonneg _) hτ
  rw [green_expansion_of_sandwich ρ roots hsandwich]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  apply (norm_five_terms_bound _ _ _ _ _).trans
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add h₁ h₂) h₃) h₄) h₅
  exact hsum.trans (by unfold greenEntryMajorant; linarith)

theorem uniform_green_entries (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℝ, 0 < B ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → boundaryScalar ρ n ≠ 0 ∧
        ∀ j : ℕ, j ≤ n → ∀ ell : ℕ, ell < n →
          ∀ r : Fin 4, ∀ s : Fin 2, ‖greenKernel ρ n j ell r s‖ ≤ B := by
  obtain ⟨roots, hroots⟩ := four_roots ρ hρ
  obtain ⟨hγ, hsandwich⟩ := dominant_projector ρ hρ roots hroots
  obtain ⟨C, D, hC, hD, hR, n0, hn0, htail⟩ := spectral_tail_bounds ρ hρ roots hroots
  have hμ : 1 < ‖roots 3‖ := hroots.2.2.2.2.2
  have hμ0 : roots 3 ≠ 0 := norm_pos_iff.mp (lt_trans zero_lt_one hμ)
  have hgpos : 0 < ‖dominantGamma ρ roots‖ := norm_pos_iff.mpr hγ
  let P : ℝ := spectralNorm (spectralProjector ρ roots 3)
  let G : ℝ := forcingEntryBound ρ
  let τ : ℝ := 2 / ‖dominantGamma ρ roots‖
  have hP : 0 ≤ P := spectralNorm_nonneg _
  have hG : 0 ≤ G := (forcingEntryBound_pos ρ).le
  have hτ : 0 ≤ τ := (div_pos (by norm_num) hgpos).le
  have hL : 0 ≤ D + 2 := by linarith
  refine ⟨greenEntryMajorant C (D + 2) P G τ,
    greenEntryMajorant_pos C (D + 2) P G τ hC.le hL hP hG hτ, n0, hn0, ?_⟩
  intro n hn
  obtain ⟨ha, hd, herr⟩ := htail n hn
  refine ⟨ha, ?_⟩
  intro j hj ell hell r s
  have haexp : boundaryScalar ρ n =
      dominantGamma ρ roots * roots 3 ^ n * normalizedBoundary ρ roots n := by
    unfold normalizedBoundary
    field_simp [hγ, hμ0] <;> ring
  have hpower (k : ℕ) (hk : k ≤ n) :
      ‖(boundaryScalar ρ n)⁻¹ * roots 3 ^ k‖ ≤ τ := by
    rw [haexp]
    exact inverse_scaled_power_bound _ _ _ hγ hμ hd n k hk
  have hinv : ‖(boundaryScalar ρ n)⁻¹‖ ≤ τ := by
    simpa only [pow_zero, mul_one] using hpower 0 (Nat.zero_le n)
  have hleading : ‖greenLeadingCoefficient ρ roots n j ell‖ ≤ D + 2 := by
    unfold greenLeadingCoefficient
    rw [haexp]
    exact green_leading_bound _ _ _ hγ hμ hd D hD.le n j ell hj hell herr
  exact green_entry_bound_of_estimates ρ roots hsandwich C (D + 2) P G τ
    hC.le hL hP hG hτ (fun a b => norm_entry_le_spectralNorm _ a b)
    (fun k a b => (norm_entry_le_spectralNorm _ a b).trans (hR k))
    (forcing_entry_bound ρ) n j ell hleading (hpower j hj)
    (hpower (n - 1 - ell) (by omega)) hinv r s

#assert_trust kernel uniform_green_entries
#print axioms uniform_green_entries

end
end NLA.MF22
