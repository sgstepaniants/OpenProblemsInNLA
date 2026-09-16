/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The three nondominant modes are bounded for every natural power. Exact
scalar denominator control is then applied to the actual boundary entry.
-/
import NLA.MF22.ScalarTail
import NLA.MF22.SpectralAlgebra
import NLA.MF22.Dominant

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open scoped BigOperators

lemma spectralRemainder_three_terms (ρ : ℝ) (hρ : 0 < ρ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots) (j : ℕ) :
    spectralRemainder ρ roots j =
      (roots 0 ^ j) • spectralProjector ρ roots 0 +
      (roots 1 ^ j) • spectralProjector ρ roots 1 +
      (roots 2 ^ j) • spectralProjector ρ roots 2 := by
  rw [spectralRemainder, (spectral_projector_algebra ρ hρ roots hroots).2.2,
    Fin.sum_univ_four]
  abel

lemma spectralRemainder_bound (ρ : ℝ) (hρ : 0 < ρ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots) (j : ℕ) :
    spectralNorm (spectralRemainder ρ roots j) ≤
      spectralNorm (spectralProjector ρ roots 0) +
      spectralNorm (spectralProjector ρ roots 1) +
      spectralNorm (spectralProjector ρ roots 2) := by
  have h₀ : ‖roots 0 ^ j‖ ≤ 1 := by simp [hroots.2.2.1]
  have h₁ : ‖roots 1 ^ j‖ ≤ 1 := by simp [norm_pow, hroots.2.2.2.1]
  have h₂ : ‖roots 2 ^ j‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hroots.2.2.2.2.1.le
  rw [spectralRemainder_three_terms ρ hρ roots hroots j]
  calc
    _ ≤ spectralNorm ((roots 0 ^ j) • spectralProjector ρ roots 0 +
        (roots 1 ^ j) • spectralProjector ρ roots 1) +
        spectralNorm ((roots 2 ^ j) • spectralProjector ρ roots 2) := spectralNorm_add _ _
    _ ≤ (spectralNorm ((roots 0 ^ j) • spectralProjector ρ roots 0) +
        spectralNorm ((roots 1 ^ j) • spectralProjector ρ roots 1)) +
        spectralNorm ((roots 2 ^ j) • spectralProjector ρ roots 2) :=
      add_le_add (spectralNorm_add _ _) (le_refl _)
    _ ≤ _ := by
      simp only [spectralNorm_smul]
      exact add_le_add (add_le_add
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h₀ (spectralNorm_nonneg _))
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h₁ (spectralNorm_nonneg _)))
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h₂ (spectralNorm_nonneg _))

lemma boundaryScalar_decomposition (ρ : ℝ) (roots : Fin 4 → ℂ) (j : ℕ) :
    boundaryScalar ρ j = dominantGamma ρ roots * roots 3 ^ j +
      spectralRemainder ρ roots j 0 0 := by
  simp only [boundaryScalar, dominantGamma, spectralRemainder, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  ring

theorem spectral_tail_bounds_of_gamma (ρ : ℝ) (hρ : 0 < ρ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots)
    (hγ : dominantGamma ρ roots ≠ 0) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      (∀ j : ℕ, spectralNorm (spectralRemainder ρ roots j) ≤ C) ∧
      ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
        boundaryScalar ρ n ≠ 0 ∧
        (1 / 2 : ℝ) ≤ ‖normalizedBoundary ρ roots n‖ ∧
        ‖1 - (normalizedBoundary ρ roots n)⁻¹‖ ≤ D * (‖roots 3‖ ^ n)⁻¹ := by
  let C : ℝ := spectralNorm (spectralProjector ρ roots 0) +
    spectralNorm (spectralProjector ρ roots 1) +
    spectralNorm (spectralProjector ρ roots 2) + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith [spectralNorm_nonneg (spectralProjector ρ roots 0),
      spectralNorm_nonneg (spectralProjector ρ roots 1),
      spectralNorm_nonneg (spectralProjector ρ roots 2)]
  have hR (j : ℕ) : spectralNorm (spectralRemainder ρ roots j) ≤ C := by
    have h := spectralRemainder_bound ρ hρ roots hroots j
    dsimp [C]
    linarith
  have hr (j : ℕ) : ‖spectralRemainder ρ roots j 0 0‖ ≤ C :=
    (norm_entry_le_spectralNorm _ _ _).trans (hR j)
  obtain ⟨D, hD, n0, hn0, hn⟩ := scalar_dominant_tail
    (dominantGamma ρ roots) (roots 3) hγ hroots.2.2.2.2.2
    (fun j => spectralRemainder ρ roots j 0 0) C hC hr
  refine ⟨C, D, hC, hD, hR, n0, hn0, ?_⟩
  intro n hn'
  have he := hn n hn'
  rw [← boundaryScalar_decomposition] at he
  exact he

theorem spectral_tail_bounds (ρ : ℝ) (hρ : 0 < ρ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      (∀ j : ℕ, spectralNorm (spectralRemainder ρ roots j) ≤ C) ∧
      ∃ n0 : ℕ, 1 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
        boundaryScalar ρ n ≠ 0 ∧
        (1 / 2 : ℝ) ≤ ‖normalizedBoundary ρ roots n‖ ∧
        ‖1 - (normalizedBoundary ρ roots n)⁻¹‖ ≤ D * (‖roots 3‖ ^ n)⁻¹ := by
  exact spectral_tail_bounds_of_gamma ρ hρ roots hroots
    (dominant_projector ρ hρ roots hroots).1

#assert_trust kernel spectral_tail_bounds_of_gamma
#print axioms spectral_tail_bounds_of_gamma
#assert_trust kernel spectral_tail_bounds
#print axioms spectral_tail_bounds

end NLA.MF22
