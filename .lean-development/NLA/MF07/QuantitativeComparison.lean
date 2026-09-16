/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical proof:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The arbitrary compact family is never discretized. Approximate extremal norms
are constructed for each a > 1; a one-sided continuity argument then removes a.
The capped diagonal weights have condition number at most s^(d-1).
-/
import NLA.MF07.Similarity

set_option autoImplicit false
set_option leancert.trust "kernel"
open Filter Topology

noncomputable section
namespace NLA.MF07

lemma applyMatrix_sub {d : ℕ} (A B : Square d) (x : EuclideanVector d) :
    applyMatrix (A - B) x = applyMatrix A x - applyMatrix B x := by
  simp [applyMatrix, map_sub]

lemma diagonalDamping_add {d : ℕ} (h : Fin d → ℝ) (A B : Square d) :
    diagonalDamping h (A + B) = diagonalDamping h A + diagonalDamping h B := by
  dsimp [diagonalDamping]
  noncomm_ring

lemma diagonalDamping_upperWeightPart {d : ℕ} (h : Fin d → ℝ) (A : Square d) :
    diagonalDamping h (upperWeightPart h A) = upperWeightPart h (diagonalDamping h A) := by
  ext i j
  rw [diagonalDamping_apply]
  by_cases hij : h j < h i <;> simp [upperWeightPart, hij, diagonalDamping_apply]

lemma word_quantitative_comparison_above_one {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hne : M.Nonempty)
    (hr : jointSpectralRadius M = 1) (s a : ℝ) (hs : 1 ≤ s) (ha : 1 < a)
    (z : List (Square d)) (hz : WordIn M z) :
    spectralNorm (matrixProduct z) ≤ (d : ℝ) * s ^ (d - 1) *
      (a + 2 * (d : ℝ) ^ 2 * familyNorm M / s) ^ z.length := by
  obtain ⟨Q, σ, w, hQ, hσm, hσp, hw, hwb, hgen, hentry⟩ :=
    rounded_extremal_norm hd M hM hne hr a ha
  obtain ⟨τ, hτb, hτm, hhm, hwide⟩ := exists_capped_weights hd σ hσm hσp s hs
  let h : Fin d → ℝ := fun i => σ i / τ i
  let B : Square d → Square d := rotatedGenerator Q σ
  let E : Square d → Square d := fun A => upperWeightPart h (B A)
  let C : Square d → Square d := fun A => B A - E A
  let E' : Square d → Square d := fun A => diagonalDamping h (E A)
  let C' : Square d → Square d := fun A => diagonalDamping h (C A)
  let e : ℝ := (d : ℝ) * familyNorm M / s
  let u : ℝ := a + (d : ℝ) * e
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd1 : 1 ≤ (d : ℝ) := by exact_mod_cast hd
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hL : 0 ≤ familyNorm M := (family_norm_maximum hd M hM hne).1
  have he : 0 ≤ e := div_nonneg (mul_nonneg hd0 hL) hspos.le
  have hu : 0 ≤ u := add_nonneg (by linarith) (mul_nonneg hd0 he)
  have hτp : ∀ i, 0 < τ i := fun i => lt_of_lt_of_le zero_lt_one (hτb i).1
  have hhp : ∀ i, 0 < h i := fun i => div_pos (hσp i) (hτp i)
  have hσ0 : ∀ i, σ i ≠ 0 := fun i => (hσp i).ne'
  have hτ0 : ∀ i, τ i ≠ 0 := fun i => (hτp i).ne'
  have hE : ∀ A ∈ M, spectralNorm (E A) ≤ e := by
    intro A hA
    have hbe : ∀ i j, ‖E A i j‖ ≤ familyNorm M / s :=
      upperWeightPart_entry_bound h (B A) _ (div_nonneg hL hspos.le) (by
        intro i j hij
        exact (hentry A hA i j).trans
          (divided_weight_entry_bound hL hspos (hσp i) (hwide i j hij).1))
    simpa only [e, mul_div_assoc] using
      spectralNorm_le_card_mul_entry_bound (E A) _ (div_nonneg hL hspos.le) hbe
  have hCgen : ∀ A ∈ M, ∀ x, w (applyMatrix (C A) x) ≤ u * w x := by
    intro A hA x
    have hEnorm : ‖applyMatrix (E A) x‖ ≤ e * ‖x‖ :=
      (norm_applyMatrix_le _ _).trans
        (mul_le_mul_of_nonneg_right (hE A hA) (norm_nonneg x))
    calc
      w (applyMatrix (C A) x) ≤ w (applyMatrix (B A) x) + w (applyMatrix (E A) x) := by
        change w (applyMatrix (B A - E A) x) ≤ _
        rw [applyMatrix_sub, sub_eq_add_neg]
        simpa only [complexNorm_neg hw] using
          hw.2.2.1 (applyMatrix (B A) x) (-applyMatrix (E A) x)
      _ ≤ a * w x + (d : ℝ) * ‖applyMatrix (E A) x‖ :=
        add_le_add (hgen A hA x) (hwb _).2
      _ ≤ a * w x + (d : ℝ) * (e * ‖x‖) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hEnorm hd0)
      _ ≤ a * w x + (d : ℝ) * (e * w x) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hwb x).1 he) hd0)
      _ = u * w x := by dsimp [u]; ring
  have hCprod : ∀ zz : List (Square d), WordIn M zz →
      spectralNorm (matrixProduct (zz.map C')) ≤ (d : ℝ) * u ^ zz.length := by
    intro zz hzz
    have hlower : ∀ A ∈ zz.map C, LowerForWeights h A := by
      intro A hA
      obtain ⟨A₀, _, rfl⟩ := List.mem_map.mp hA
      exact subtract_upperWeightPart_lower h (B A₀)
    have hdamp := damped_lower_product_bound h hhm hhp (zz.map C) hlower
    have hold := spectralNorm_product_of_norm M C w (d : ℝ) u hd0 hu hwb hCgen zz hzz
    simpa only [List.map_map, Function.comp_def, C'] using hdamp.trans hold
  have hE' : ∀ A ∈ M, spectralNorm (E' A) ≤ e := by
    intro A hA
    have heq : E' A = upperWeightPart h (rotatedGenerator Q τ A) := by
      dsimp only [E', E, B]
      rw [diagonalDamping_upperWeightPart,
        rotatedGenerator_change_weights Q σ τ hσ0 hτ0]
    rw [heq]
    have hb : ∀ i j, h j < h i →
        ‖rotatedGenerator Q τ A i j‖ ≤ familyNorm M / s := by
      intro i j hij
      exact (rotatedGenerator_entry_bound hd hQ τ hτp A (familyNorm M)
        ((family_norm_maximum hd M hM hne).2.2 A hA) i j).trans
          (divided_weight_entry_bound hL hspos (hτp i) (hwide i j hij).2)
    have hbe := upperWeightPart_entry_bound h (rotatedGenerator Q τ A) _
      (div_nonneg hL hspos.le) hb
    simpa only [e, mul_div_assoc] using
      spectralNorm_le_card_mul_entry_bound _ _ (div_nonneg hL hspos.le) hbe
  have hsum : (fun A => C' A + E' A) = rotatedGenerator Q τ := by
    funext A
    calc
      C' A + E' A = diagonalDamping h (C A + E A) := (diagonalDamping_add h _ _).symm
      _ = diagonalDamping h (B A) := by rw [show C A + E A = B A by exact sub_add_cancel _ _]
      _ = rotatedGenerator Q τ A := rotatedGenerator_change_weights Q σ τ hσ0 hτ0 A
  have hnew := interspersed_product_bound M C' E' (d : ℝ) u e hd1 hu he hCprod hE' z hz
  rw [hsum, rotatedGenerator_product hQ τ hτ0] at hnew
  have hrate : u + (d : ℝ) * e = a + 2 * (d : ℝ) ^ 2 * familyNorm M / s := by
    dsimp [u, e]
    ring
  rw [hrate] at hnew
  calc
    spectralNorm (matrixProduct z) ≤
        s ^ (d - 1) * spectralNorm (rotatedGenerator Q τ (matrixProduct z)) :=
      spectralNorm_unrotate_le hQ τ _ (pow_nonneg hspos.le _) hτb _
    _ ≤ s ^ (d - 1) * ((d : ℝ) *
        (a + 2 * (d : ℝ) ^ 2 * familyNorm M / s) ^ z.length) :=
      mul_le_mul_of_nonneg_left hnew (pow_nonneg hspos.le _)
    _ = _ := by ring

theorem quantitative_comparison {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (hr : jointSpectralRadius M = 1)
    (s : ℝ) (hs : 1 ≤ s) (n : ℕ) :
    familyGrowth M n ≤ (d : ℝ) * s ^ (d - 1) *
      (1 + 2 * (d : ℝ) ^ 2 * familyNorm M / s) ^ n := by
  have hbound : ∀ a : ℝ, 1 < a → familyGrowth M n ≤
      (d : ℝ) * s ^ (d - 1) * (a + 2 * (d : ℝ) ^ 2 * familyNorm M / s) ^ n := by
    intro a ha
    obtain ⟨z, hzlen, hz, he⟩ := familyGrowth_attained M hM hne n
    rw [← he, ← hzlen]
    exact word_quantitative_comparison_above_one hd M hM hne hr s a hs ha z hz
  have hcontinuous : Continuous (fun a : ℝ =>
      (d : ℝ) * s ^ (d - 1) * (a + 2 * (d : ℝ) ^ 2 * familyNorm M / s) ^ n) := by
    fun_prop
  have hlimit := hcontinuous.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[Set.Ioi (1 : ℝ)] 1 ≤ 𝓝 1)
  apply ge_of_tendsto hlimit
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact hbound a ha

#print axioms quantitative_comparison
#assert_trust kernel quantitative_comparison

end NLA.MF07
