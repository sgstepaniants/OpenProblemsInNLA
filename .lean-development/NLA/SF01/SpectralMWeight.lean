/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, Cambridge DAMTP.

The original spectral M-matrix premise implies positivity of the particular
inverse weight C⁻¹1. No supplied positive-weight surrogate is used.
-/
import NLA.SF01.UnitWeightContinuity
import NLA.SF01.PositivePath

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped Matrix

lemma spectralHomotopy_weight_positive {n : ℕ} (hn : 1 ≤ n) (B : Square n)
    (hB : EntrywiseNonnegative B) (s : ℝ) (hs : spectralRadius B < s) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i, 0 < weightVector (spectralHomotopy s B t) i := by
  have hspos : 0 < s := (complex_spectral_radius_semantics hn B).2.2.1.trans_lt hs
  apply continuous_positive_coordinates hn _ (spectralHomotopy_weight_continuousOn hn B s hs)
  · apply scalar_system_positive s hspos
    have he := unit_weightVector_equation _
      (spectral_homotopy_isUnit hn B s hs 0 ⟨le_rfl, zero_le_one⟩)
    simpa only [spectralHomotopy, zero_smul, sub_zero] using he
  · intro t ht hv
    exact spectralHomotopy_nonnegative_no_zero B hB s t ht.1 _ hv
      (unit_weightVector_equation _ (spectral_homotopy_isUnit hn B s hs t ht))

theorem spectralM_positive_weight {n : ℕ} (hn : 1 ≤ n) (C : Square n)
    (hC : IsSpectralM C) :
    IsUnit C ∧ IsZMatrix C ∧ (∀ i, 0 < weightVector C i) ∧
      C *ᵥ weightVector C = (fun _ => 1) := by
  rcases hC with ⟨s, B, hB, heq, hs⟩
  have hend : C = spectralHomotopy s B 1 := by
    simpa only [spectralHomotopy, one_smul] using heq
  have hunit : IsUnit C := by
    rw [hend]
    exact spectral_homotopy_isUnit hn B s hs 1 ⟨zero_le_one, le_rfl⟩
  have hZ : IsZMatrix C := by
    intro i j hij
    have hij_eq : C i j = -B i j := by
      rw [heq]
      simp [Matrix.one_apply, hij]
    rw [hij_eq]
    exact neg_nonpos.mpr (hB i j)
  refine ⟨hunit, hZ, ?_, unit_weightVector_equation C hunit⟩
  have hw := spectralHomotopy_weight_positive hn B hB s hs 1 ⟨zero_le_one, le_rfl⟩
  simpa only [← hend] using hw

end
end NLA.SF01
