/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, Cambridge DAMTP.

Actual inverse equations and continuity; no positive weight is assumed.
-/
import NLA.SF01.SpectralHomotopy
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma unit_weightVector_equation {n : ℕ} (C : Square n) (hC : IsUnit C) :
    C *ᵥ weightVector C = (fun _ => 1) := by
  rw [weightVector, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hC), Matrix.one_mulVec]

lemma unit_inverse_continuousAt {n : ℕ} (C : Square n) (hC : IsUnit C) :
    ContinuousAt (fun X : Square n => X⁻¹) C := by
  have hdet : C.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det C).mp hC).ne_zero
  apply continuousAt_matrix_inv C
  simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet)

lemma unit_weightVector_continuousAt {n : ℕ} (C : Square n) (hC : IsUnit C) :
    ContinuousAt (fun X : Square n => weightVector X) C := by
  have hmul : Continuous (fun X : Square n => X *ᵥ (fun _ : Fin n => (1 : ℝ))) :=
    continuous_id.matrix_mulVec continuous_const
  exact hmul.continuousAt.comp (unit_inverse_continuousAt C hC)

lemma spectralHomotopy_continuous {n : ℕ} (s : ℝ) (B : Square n) :
    Continuous (fun t : ℝ => spectralHomotopy s B t) := by
  exact continuous_const.sub (continuous_id.smul continuous_const)

lemma spectralHomotopy_weight_continuousOn {n : ℕ} (hn : 1 ≤ n) (B : Square n)
    (s : ℝ) (hs : spectralRadius B < s) :
    ContinuousOn (fun t : ℝ => weightVector (spectralHomotopy s B t))
      (Set.Icc (0 : ℝ) 1) := by
  intro t ht
  exact ((unit_weightVector_continuousAt _ (spectral_homotopy_isUnit hn B s hs t ht)).comp
    (spectralHomotopy_continuous s B).continuousAt).continuousWithinAt

lemma spectralHomotopy_mulVec {n : ℕ} (s : ℝ) (B : Square n) (t : ℝ) (v : Vector n) :
    spectralHomotopy s B t *ᵥ v = s • v - t • (B *ᵥ v) := by
  simp only [spectralHomotopy, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

lemma scalar_system_positive {n : ℕ} (s : ℝ) (hs : 0 < s) (v : Vector n)
    (hv : (s • (1 : Square n)) *ᵥ v = (fun _ => 1)) : ∀ i, 0 < v i := by
  intro i
  have hi := congrFun hv i
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul] at hi
  by_contra hn
  have hnonpos : s * v i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hs.le (le_of_not_gt hn)
  linarith

lemma spectralHomotopy_nonnegative_no_zero {n : ℕ} (B : Square n)
    (hB : EntrywiseNonnegative B) (s t : ℝ) (ht : 0 ≤ t) (v : Vector n)
    (hv : ∀ i, 0 ≤ v i) (heq : spectralHomotopy s B t *ᵥ v = (fun _ => 1)) :
    ∀ i, v i ≠ 0 := by
  intro i hzero
  have hsum : 0 ≤ (B *ᵥ v) i :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hB i j) (hv j))
  rw [spectralHomotopy_mulVec] at heq
  have hi : s * v i - t * (B *ᵥ v) i = 1 := by
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using congrFun heq i
  have hprod : 0 ≤ t * (B *ᵥ v) i := mul_nonneg ht hsum
  rw [hzero, mul_zero, zero_sub] at hi
  linarith

end
end NLA.SF01
