/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Uniform Green entries imply bounds on the actual inverse. The true Euclidean
operator norms on all 2n coordinates give the sufficient quadratic exponent
for the complete original existential polynomial-conditioning question.
-/
import NLA.MF22.GreenEntryBounds
import NLA.MF22.GreenInverse
import NLA.MF22.SourceBounds

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22

lemma blockIndex_card (n : ℕ) : Fintype.card (BlockIndex n) = n * 2 := by
  simp [BlockIndex]

theorem eventual_inverse_entries (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ B : ℝ, 0 < B ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → (toeplitz ρ n).det ≠ 0 ∧
        ∀ r s : BlockIndex n, ‖(toeplitz ρ n)⁻¹ r s‖ ≤ B := by
  obtain ⟨B, hB, n0, hn0, hgreen⟩ := uniform_green_entries ρ hρ
  refine ⟨80 * B, mul_pos (by norm_num) hB, n0, hn0, ?_⟩
  intro n hn
  have hnpos : 1 ≤ n := le_trans hn0 hn
  obtain ⟨ha, hentries⟩ := hgreen n hn
  have hinverse := green_inverse ρ hρ n hnpos ha
  refine ⟨hinverse.2.2.2.1, ?_⟩
  intro r s
  have hQ : ‖inverseCandidate ρ n r s‖ ≤ B := by
    by_cases hr : r.2 = 0
    · rw [inverseCandidate, if_pos hr]
      exact hentries r.1.val r.1.isLt.le s.1.val s.1.isLt 0 s.2
    · rw [inverseCandidate, if_neg hr]
      exact hentries (r.1.val + 1) (by have := r.1.isLt; omega)
        s.1.val s.1.isLt 1 s.2
  rw [hinverse.2.2.2.2, Matrix.smul_apply, norm_smul]
  have h80 : ‖(80 : ℂ)‖ = (80 : ℝ) := by norm_num
  rw [h80]
  exact mul_le_mul_of_nonneg_left hQ (by norm_num)

theorem eventual_quadratic_conditioning (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ K : ℝ, 0 < K ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → (toeplitz ρ n).det ≠ 0 ∧
        conditionNumber (toeplitz ρ n) ≤ ENNReal.ofReal (K * (n : ℝ) ^ 2) := by
  obtain ⟨B, hB, n0, hn0, hinverse⟩ := eventual_inverse_entries ρ hρ
  have hc : 0 < 2 + ρ := by linarith
  refine ⟨4 * (2 + ρ) * B, mul_pos (mul_pos (by norm_num) hc) hB, n0, hn0, ?_⟩
  intro n hn
  obtain ⟨hdet, hentries⟩ := hinverse n hn
  refine ⟨hdet, ?_⟩
  rw [conditionNumber, if_neg hdet]
  apply ENNReal.ofReal_le_ofReal
  have hH := complex_entry_norm_bound (BlockIndex n) (toeplitz ρ n) (2 + ρ)
    hc.le (source_entry_bound ρ hρ n)
  have hInv := complex_entry_norm_bound (BlockIndex n) (toeplitz ρ n)⁻¹ B hB.le hentries
  rw [blockIndex_card] at hH hInv
  have hp := mul_le_mul hH hInv (spectralNorm_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) hc.le)
  exact hp.trans (le_of_eq (by push_cast; ring))

theorem polynomial_conditioning (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ K α : ℝ, 0 < K ∧ 0 ≤ α ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → (toeplitz ρ n).det ≠ 0 ∧
        conditionNumber (toeplitz ρ n) ≤ ENNReal.ofReal (K * Real.rpow (n : ℝ) α) := by
  obtain ⟨K, hK, n0, hn0, hquad⟩ := eventual_quadratic_conditioning ρ hρ
  refine ⟨K, 2, hK, by norm_num, n0, hn0, ?_⟩
  intro n hn
  have h := hquad n hn
  simpa only [Real.rpow_eq_pow, Real.rpow_two] using h

#assert_trust kernel eventual_inverse_entries
#print axioms eventual_inverse_entries
#assert_trust kernel eventual_quadratic_conditioning
#print axioms eventual_quadratic_conditioning
#assert_trust kernel polynomial_conditioning
#print axioms polynomial_conditioning

end NLA.MF22
