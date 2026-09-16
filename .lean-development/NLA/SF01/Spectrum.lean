/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization of Matthew J. Colbrook's SF-01 result, Cambridge DAMTP.

The original complex algebraic spectrum is finite and nonempty in positive
dimension. Its radius is the actual attained maximum, not a surrogate norm.
-/
import NLA.SF01.Complexification
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Order.ConditionallyCompleteLattice.Finset

set_option autoImplicit false

namespace NLA.SF01
noncomputable section

lemma complexSpectrum_finite {n : ℕ} (B : Square n) : (complexSpectrum B).Finite := by
  exact Matrix.finite_spectrum (complexify B)

lemma complexSpectrum_nonempty {n : ℕ} (hn : 1 ≤ n) (B : Square n) :
    (complexSpectrum B).Nonempty := by
  letI : Nonempty (Fin n) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩⟩
  exact spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ (complexify B)

theorem complex_spectral_radius_semantics {n : ℕ} (hn : 1 ≤ n) (B : Square n) :
    (complexSpectrum B).Finite ∧ (complexSpectrum B).Nonempty ∧
    0 ≤ spectralRadius B ∧
    (∃ z ∈ complexSpectrum B, ‖z‖ = spectralRadius B) ∧
    ∀ z ∈ complexSpectrum B, ‖z‖ ≤ spectralRadius B := by
  have hf := complexSpectrum_finite B
  have he := complexSpectrum_nonempty hn B
  have hnf : ((fun z : ℂ => ‖z‖) '' complexSpectrum B).Finite := hf.image _
  have hne : ((fun z : ℂ => ‖z‖) '' complexSpectrum B).Nonempty := he.image _
  have hm : spectralRadius B ∈ (fun z : ℂ => ‖z‖) '' complexSpectrum B :=
    hne.csSup_mem hnf
  obtain ⟨z, hz, hzr⟩ := hm
  refine ⟨hf, he, ?_, ⟨z, hz, hzr⟩, ?_⟩
  · rw [← hzr]
    exact norm_nonneg z
  · intro w hw
    exact le_csSup hnf.bddAbove ⟨w, hw, rfl⟩

theorem spectral_radius_strict_bound {n : ℕ} (hn : 1 ≤ n) (B : Square n)
    (r s : ℝ) (hrs : r < s) (hbound : ∀ z ∈ complexSpectrum B, ‖z‖ ≤ r) :
    spectralRadius B < s := by
  obtain ⟨_, _, _, ⟨z, hz, hzr⟩, _⟩ := complex_spectral_radius_semantics hn B
  calc
    spectralRadius B = ‖z‖ := hzr.symm
    _ ≤ r := hbound z hz
    _ < s := hrs

end
end NLA.SF01
