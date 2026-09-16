/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original norm-rounding argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Coordinate-unit and application lemmas follow the campaign's MF/MI Euclidean
coordinate interfaces and Mathlib's PiL2 construction. All bounds here concern
actual vectors and norms, not an abstract supplied comparison constant.
-/
import NLA.MF07.ProductEnvelope
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF07

@[simp] lemma applyMatrix_zero {d : ℕ} (A : Square d) :
    applyMatrix A (0 : EuclideanVector d) = 0 := by
  simp [applyMatrix]

lemma complexNorm_zero {d : ℕ} {v : EuclideanVector d → ℝ} (hv : IsComplexNorm v) : v 0 = 0 :=
  (hv.2.1 0).mpr rfl

lemma complexNorm_neg {d : ℕ} {v : EuclideanVector d → ℝ} (hv : IsComplexNorm v)
    (x : EuclideanVector d) : v (-x) = v x := by
  simpa using hv.2.2.2 (-1) x

lemma complexNorm_sum {d : ℕ} {v : EuclideanVector d → ℝ} (hv : IsComplexNorm v)
    {ι : Type*} (s : Finset ι) (f : ι → EuclideanVector d) :
    v (∑ i ∈ s, f i) ≤ ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [complexNorm_zero hv]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (hv.2.2.1 _ _).trans (add_le_add le_rfl ih)

lemma complexNorm_continuous {d : ℕ} {v : EuclideanVector d → ℝ}
    (hv : IsComplexNorm v) (c : ℝ) (hc : 0 ≤ c)
    (hupper : ∀ x, v x ≤ c * ‖x‖) : Continuous v := by
  have hlip : LipschitzWith (NNReal.mk c hc) v := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hxy : v x - v y ≤ c * ‖x-y‖ := by
      have ht := hv.2.2.1 (x-y) y
      have hu := hupper (x-y)
      simp only [sub_add_cancel] at ht
      linarith
    have hyx : v y - v x ≤ c * ‖x-y‖ := by
      have ht := hv.2.2.1 (y-x) x
      have hu := hupper (y-x)
      simp only [sub_add_cancel, norm_sub_rev y x] at ht hu
      linarith
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_mk] using
      (abs_sub_le_iff.mpr ⟨hxy, hyx⟩)
  exact hlip.continuous

lemma complexNorm_unitBall_compact {d : ℕ} {v : EuclideanVector d → ℝ}
    (hv : IsComplexNorm v) (c : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ x, ‖x‖ ≤ v x ∧ v x ≤ c * ‖x‖) :
    IsCompact {x : EuclideanVector d | v x ≤ 1} := by
  have hclosed : IsClosed {x : EuclideanVector d | v x ≤ 1} :=
    isClosed_le (complexNorm_continuous hv c hc (fun x => (hbound x).2)) continuous_const
  apply (isCompact_closedBall (0 : EuclideanVector d) 1).of_isClosed_subset hclosed
  intro x hx
  simpa only [Metric.mem_closedBall, dist_zero_right] using (hbound x).1.trans hx

def coordinateUnit {d : ℕ} (i : Fin d) : EuclideanVector d := EuclideanSpace.single i 1

@[simp] lemma coordinateUnit_apply {d : ℕ} (i j : Fin d) :
    coordinateUnit i j = if j = i then 1 else 0 := by
  simp [coordinateUnit, PiLp.single_apply]

@[simp] lemma coordinateUnit_norm {d : ℕ} (i : Fin d) : ‖coordinateUnit i‖ = 1 := by
  simp [coordinateUnit]

lemma continuous_coordinate {d : ℕ} (i : Fin d) :
    Continuous (fun x : EuclideanVector d => x i) := by
  let f : EuclideanVector d →ₗ[ℂ] ℂ :=
    { toFun := fun x => x i
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  exact f.continuous_of_finiteDimensional

lemma applyMatrix_coordinate {d : ℕ} (A : Square d) (x : EuclideanVector d) (i : Fin d) :
    applyMatrix A x i = ∑ j, A i j * x j := by
  -- toEuclideanCLM uses the canonical coordinate orthonormal basis.
  rfl

lemma coordinate_norm_le {d : ℕ} (x : EuclideanVector d) (i : Fin d) : ‖x i‖ ≤ ‖x‖ := by
  have hs : ‖x i‖^2 ≤ ‖x‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖x j‖) (Finset.mem_univ i)
  nlinarith [norm_nonneg (x i), norm_nonneg x]

lemma spectralNorm_entry_bound {d : ℕ} (A : Square d) (i j : Fin d) :
    ‖A i j‖ ≤ spectralNorm A := by
  have hc := coordinate_norm_le (applyMatrix A (coordinateUnit j)) i
  have ha := norm_applyMatrix_le A (coordinateUnit j)
  simpa [applyMatrix_coordinate] using hc.trans ha

lemma sum_coordinate_norms_le {d : ℕ} (x : EuclideanVector d) :
    (∑ i, ‖x i‖) ≤ Real.sqrt (d : ℝ) * ‖x‖ := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
    (fun _ => (1 : ℝ)) (fun i => ‖x i‖)
  have he : (∑ i, ‖x i‖)^2 ≤ (d : ℝ) * ‖x‖^2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ← EuclideanSpace.norm_sq_eq] using hs
  have hd : Real.sqrt (d : ℝ)^2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have hsum : 0 ≤ ∑ i, ‖x i‖ := Finset.sum_nonneg fun i _ => norm_nonneg (x i)
  have hr : 0 ≤ Real.sqrt (d : ℝ) * ‖x‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x)
  nlinarith

lemma norm_le_sqrt_card_mul_coordinate_bound {d : ℕ} (x : EuclideanVector d)
    (b : ℝ) (hb : 0 ≤ b) (hxb : ∀ i, ‖x i‖ ≤ b) :
    ‖x‖ ≤ Real.sqrt (d : ℝ) * b := by
  have hs : ‖x‖^2 ≤ (d : ℝ) * b^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      ∑ i, ‖x i‖^2 ≤ ∑ _i : Fin d, b^2 := by
        exact Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg (x i)) (hxb i) 2
      _ = (d : ℝ) * b^2 := by simp
  have hd : Real.sqrt (d : ℝ)^2 = d := Real.sq_sqrt (Nat.cast_nonneg d)
  have hr : 0 ≤ Real.sqrt (d : ℝ) * b := mul_nonneg (Real.sqrt_nonneg _) hb
  nlinarith [norm_nonneg x]

#print axioms complexNorm_unitBall_compact
#assert_trust kernel complexNorm_unitBall_compact
#print axioms sum_coordinate_norms_le
#assert_trust kernel sum_coordinate_norms_le

end NLA.MF07
