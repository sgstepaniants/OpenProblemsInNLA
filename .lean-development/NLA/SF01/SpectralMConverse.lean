/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, Cambridge DAMTP.

Construct the original sI-B representation from the explicit positive weight.
Finite maxima are symbolic and attained; no numerical eigenvalues are used.
-/
import NLA.SF01.WeightedSpectrum

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

theorem weighted_Z_spectralM {n : ℕ} (hn : 1 ≤ n) (C : Square n)
    (v : Vector n) (hZ : IsZMatrix C) (hv : PositiveWeight C v) :
    IsSpectralM C := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩, Finset.mem_univ _⟩
  let s : ℝ := (Finset.univ : Finset (Fin n)).sup' hne (fun i => C i i)
  let B : Square n := s • (1 : Square n) - C
  have hB : EntrywiseNonnegative B := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hd : C i i ≤ s := Finset.le_sup' (fun l => C l l) (Finset.mem_univ i)
      simpa only [B, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
        smul_eq_mul, mul_one] using sub_nonneg.mpr hd
    · have he : B i j = -C i j := by simp [B, Matrix.one_apply, hij]
      rw [he]
      exact neg_nonneg.mpr (hZ i j hij)
  have hprod : ∀ i, (B *ᵥ v) i = s * v i - (C *ᵥ v) i := by
    intro i
    simp only [B, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hratio : ∀ i, (B *ᵥ v) i / v i < s := by
    intro i
    apply (div_lt_iff₀ (hv.1 i)).mpr
    rw [hprod]
    linarith [hv.2 i]
  let r : ℝ := (Finset.univ : Finset (Fin n)).sup' hne (fun i => (B *ᵥ v) i / v i)
  have hrs : r < s := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun j => (B *ᵥ v) j / v j)
    calc
      r = (B *ᵥ v) i / v i := hi
      _ < s := hratio i
  have hrow : ∀ i, (B *ᵥ v) i ≤ r * v i := by
    intro i
    exact (div_le_iff₀ (hv.1 i)).mp
      (Finset.le_sup' (fun j => (B *ᵥ v) j / v j) (Finset.mem_univ i))
  have hspec : spectralRadius B < s :=
    spectral_radius_strict_bound hn B r s hrs
      (weighted_complexSpectrum_bound hn B hB v hv.1 r hrow)
  refine ⟨s, B, hB, ?_, hspec⟩
  dsimp only [B]
  abel

end
end NLA.SF01
