/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization of Matthew J. Colbrook's SF-01 result, Cambridge DAMTP.

Actual nonsingularity on the entire spectral homotopy. Entrywise
nonnegativity of B is not needed for this contract and is not assumed.
-/
import NLA.SF01.Spectrum

set_option autoImplicit false

namespace NLA.SF01
noncomputable section

lemma real_scalar_identity_isUnit (n : ℕ) (s : ℝ) (hs : s ≠ 0) :
    IsUnit (s • (1 : Square n)) := by
  have h : IsUnit (algebraMap ℝ (Square n) s) :=
    IsUnit.map (algebraMap ℝ (Square n)) (isUnit_iff_ne_zero.mpr hs)
  simpa only [Algebra.algebraMap_eq_smul_one] using h

theorem spectral_homotopy_isUnit {n : ℕ} (hn : 1 ≤ n) (B : Square n)
    (s : ℝ) (hs : spectralRadius B < s) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsUnit (spectralHomotopy s B t) := by
  classical
  have hsem := complex_spectral_radius_semantics hn B
  have hspos : 0 < s := hsem.2.2.1.trans_lt hs
  by_cases htzero : t = 0
  · subst t
    simpa only [spectralHomotopy, zero_smul, sub_zero] using
      real_scalar_identity_isUnit n s hspos.ne'
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm htzero)
  have hst : s ≤ s / t := by
    apply (le_div_iff₀ htpos).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 hspos.le
  have hnot : ((s / t : ℝ) : ℂ) ∉ complexSpectrum B := by
    intro hz
    have hb := hsem.2.2.2.2 _ hz
    rw [Complex.norm_of_nonneg (div_pos hspos htpos).le] at hb
    exact (not_lt_of_ge hst) (hb.trans_lt hs)
  have hcomplex : IsUnit
      (((s / t : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - complexify B) := by
    by_contra hunit
    apply hnot
    change ¬ IsUnit (algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) ((s / t : ℝ) : ℂ) -
      complexify B)
    simpa only [Algebra.algebraMap_eq_smul_one] using hunit
  have hreal : IsUnit ((s / t) • (1 : Square n) - B) := by
    apply (complexify_isUnit_iff _).mp
    simpa only [complexify_sub, complexify_smul, complexify_one] using hcomplex
  have hts : t * (s / t) = s := by
    calc
      t * (s / t) = s * (t * t⁻¹) := by rw [div_eq_mul_inv, mul_left_comm]
      _ = s := by rw [mul_inv_cancel₀ htzero, mul_one]
  have he : (t • (1 : Square n)) * ((s / t) • (1 : Square n) - B) =
      spectralHomotopy s B t := by
    simp only [Matrix.smul_mul, one_mul, smul_sub, smul_smul, hts, spectralHomotopy]
  rw [← he]
  exact (real_scalar_identity_isUnit n t htzero).mul hreal

end
end NLA.SF01
