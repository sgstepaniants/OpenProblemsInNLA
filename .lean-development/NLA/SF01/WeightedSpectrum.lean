/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, Cambridge DAMTP.

Actual complex eigenvectors and a symbolic weighted maximum-component bound.
No diagonalization, numerical spectrum, or norm-radius surrogate is assumed.
-/
import NLA.SF01.Spectrum
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma complexSpectrum_hasEigenvector {n : ℕ} (B : Square n) (μ : ℂ)
    (hμ : μ ∈ complexSpectrum B) :
    ∃ z : Fin n → ℂ, z ≠ 0 ∧ complexify B *ᵥ z = μ • z := by
  have hs : μ ∈ spectrum ℂ (Matrix.toLinAlgEquiv' (complexify B)) := by
    rw [AlgEquiv.spectrum_eq]
    exact hμ
  have he : Module.End.HasEigenvalue (Matrix.toLinAlgEquiv' (complexify B)) μ :=
    Module.End.HasEigenvalue.of_mem_spectrum hs
  obtain ⟨z, hz, hne⟩ := he.exists_hasEigenvector
  refine ⟨z, hne, ?_⟩
  simpa only [Matrix.toLinAlgEquiv'_apply] using Module.End.mem_eigenspace_iff.mp hz

lemma complexify_mulVec_norm_le {n : ℕ} (B : Square n)
    (hB : EntrywiseNonnegative B) (z : Fin n → ℂ) (i : Fin n) :
    ‖(complexify B *ᵥ z) i‖ ≤ ∑ j : Fin n, B i j * ‖z j‖ := by
  calc
    ‖(complexify B *ᵥ z) i‖ = ‖∑ j : Fin n, (B i j : ℂ) * z j‖ := rfl
    _ ≤ ∑ j : Fin n, ‖(B i j : ℂ) * z j‖ := norm_sum_le _ _
    _ = ∑ j : Fin n, B i j * ‖z j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, Complex.norm_of_nonneg (hB i j)]

lemma weighted_eigenvector_bound {n : ℕ} (hn : 1 ≤ n) (B : Square n)
    (hB : EntrywiseNonnegative B) (v : Vector n) (hv : ∀ i, 0 < v i)
    (r : ℝ) (hrow : ∀ i, (B *ᵥ v) i ≤ r * v i)
    (μ : ℂ) (z : Fin n → ℂ) (hz : z ≠ 0) (heig : complexify B *ᵥ z = μ • z) :
    ‖μ‖ ≤ r := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩, Finset.mem_univ _⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun j => ‖z j‖ / v j)
  have hratio : ∀ j, ‖z j‖ / v j ≤ ‖z i‖ / v i := by
    intro j
    have hj := Finset.le_sup' (fun l => ‖z l‖ / v l) (Finset.mem_univ j)
    rwa [hi] at hj
  have hzi : z i ≠ 0 := by
    intro hzero
    apply hz
    funext j
    have hj := (div_le_iff₀ (hv j)).mp (hratio j)
    simp only [hzero, norm_zero, zero_div, zero_mul] at hj
    exact norm_eq_zero.mp (le_antisymm hj (norm_nonneg _))
  let R : ℝ := ‖z i‖ / v i
  have hR : 0 ≤ R := div_nonneg (norm_nonneg _) (hv i).le
  have hRi : R * v i = ‖z i‖ := div_mul_cancel₀ _ (hv i).ne'
  have hbound : ‖μ‖ * ‖z i‖ ≤ r * ‖z i‖ := by
    calc
      ‖μ‖ * ‖z i‖ = ‖(complexify B *ᵥ z) i‖ := by
        rw [heig]
        simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
      _ ≤ ∑ j : Fin n, B i j * ‖z j‖ := complexify_mulVec_norm_le B hB z i
      _ ≤ ∑ j : Fin n, B i j * (R * v j) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left
          ((div_le_iff₀ (hv j)).mp (hratio j)) (hB i j))
      _ = R * (B *ᵥ v) i := by
        simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ R * (r * v i) := mul_le_mul_of_nonneg_left (hrow i) hR
      _ = r * (R * v i) := by ring
      _ = r * ‖z i‖ := by rw [hRi]
  exact (mul_le_mul_right (norm_pos_iff.mpr hzi)).mp hbound

lemma weighted_complexSpectrum_bound {n : ℕ} (hn : 1 ≤ n) (B : Square n)
    (hB : EntrywiseNonnegative B) (v : Vector n) (hv : ∀ i, 0 < v i)
    (r : ℝ) (hrow : ∀ i, (B *ᵥ v) i ≤ r * v i) :
    ∀ μ ∈ complexSpectrum B, ‖μ‖ ≤ r := by
  intro μ hμ
  obtain ⟨z, hz, heig⟩ := complexSpectrum_hasEigenvector B μ hμ
  exact weighted_eigenvector_bound hn B hB v hv r hrow μ z hz heig

end
end NLA.SF01
