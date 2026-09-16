/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original maximal-determinant rounding argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The basis is obtained from compact determinant maximization. No Auerbach basis,
rounded norm or norm-comparison conclusion is introduced as an assumption.
-/
import NLA.MF07.NormGeometry
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF07

/-- A matrix built from genuine Euclidean columns. -/
def columnMatrix {d : ℕ} (b : Fin d → EuclideanVector d) : Square d := fun i j => b j i

def matrixColumn {d : ℕ} (T : Square d) (j : Fin d) : EuclideanVector d :=
  applyMatrix T (coordinateUnit j)

@[simp] lemma matrixColumn_apply {d : ℕ} (T : Square d) (j i : Fin d) :
    matrixColumn T j i = T i j := by
  simp [matrixColumn, applyMatrix_coordinate]

@[simp] lemma columnMatrix_matrixColumn {d : ℕ} (T : Square d) :
    columnMatrix (matrixColumn T) = T := by
  ext i j
  exact matrixColumn_apply T j i

@[simp] lemma matrixColumn_columnMatrix {d : ℕ} (b : Fin d → EuclideanVector d)
    (j : Fin d) : matrixColumn (columnMatrix b) j = b j := by
  ext i
  simp [columnMatrix]

lemma applyMatrix_eq_sum_columns {d : ℕ} (T : Square d) (z : EuclideanVector d) :
    applyMatrix T z = ∑ i, z i • matrixColumn T i := by
  ext j
  simp [applyMatrix_coordinate, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, mul_comm]

lemma matrixColumn_updateCol {d : ℕ} (T : Square d) (j k : Fin d)
    (x : EuclideanVector d) :
    matrixColumn (T.updateCol j (fun i => x i)) k =
      if k = j then x else matrixColumn T k := by
  ext i
  by_cases h : k = j
  · subst k
    simp
  · simp [Matrix.updateCol_apply, h]

lemma continuous_columnMatrix {d : ℕ} :
    Continuous (columnMatrix (d := d)) := by
  apply continuous_matrix
  intro i j
  exact (continuous_coordinate i).comp (continuous_apply j)

lemma maximal_determinant_basis {d : ℕ} {v : EuclideanVector d → ℝ}
    (hv : IsComplexNorm v) (c : ℝ) (hc : 1 ≤ c)
    (hbound : ∀ x, ‖x‖ ≤ v x ∧ v x ≤ c * ‖x‖) :
    ∃ T : Square d, T.det ≠ 0 ∧ (∀ i, v (matrixColumn T i) ≤ 1) ∧
      ∀ S : Square d, (∀ i, v (matrixColumn S i) ≤ 1) → ‖S.det‖ ≤ ‖T.det‖ := by
  classical
  let K := {x : EuclideanVector d | v x ≤ 1}
  letI : CompactSpace K := isCompact_iff_compactSpace.mp
    (complexNorm_unitBall_compact hv c (by linarith) hbound)
  letI : Nonempty K := ⟨⟨0, by simp [K, complexNorm_zero hv]⟩⟩
  let f : (Fin d → K) → ℝ := fun b => ‖(columnMatrix (fun i => (b i).val)).det‖
  have hfc : Continuous f :=
    (continuous_columnMatrix.comp
      (continuous_pi fun i => (continuous_apply i).subtype_val)).matrix_det.norm
  have hr : IsCompact (Set.range f) := isCompact_range hfc
  obtain ⟨b, hb⟩ := hr.sSup_mem (Set.range_nonempty f)
  let T := columnMatrix (fun i => (b i).val)
  have hmax : ∀ S : Square d, (∀ i, v (matrixColumn S i) ≤ 1) →
      ‖S.det‖ ≤ ‖T.det‖ := by
    intro S hS
    let bS : Fin d → K := fun i => ⟨matrixColumn S i, hS i⟩
    have hh : f bS ≤ sSup (Set.range f) := le_csSup hr.bddAbove ⟨bS, rfl⟩
    rw [← hb] at hh
    simpa only [f, bS, columnMatrix_matrixColumn, T] using hh
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  let W : Square d := (c⁻¹ : ℂ) • 1
  have hW : ∀ i, v (matrixColumn W i) ≤ 1 := by
    intro i
    have he : matrixColumn W i = (c⁻¹ : ℂ) • coordinateUnit i := by
      ext j
      simp [W, Matrix.one_apply, coordinateUnit_apply, PiLp.smul_apply]
    rw [he]
    have hh := (hbound ((c⁻¹ : ℂ) • coordinateUnit i)).2
    simpa [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hcpos, hcpos.ne'] using hh
  have hWdet : W.det ≠ 0 := by
    simp [W, Matrix.det_smul, hcpos.ne']
  have hTdet : T.det ≠ 0 := by
    have hn : 0 < ‖W.det‖ := norm_pos_iff.mpr hWdet
    exact norm_pos_iff.mp (hn.trans_le (hmax W hW))
  refine ⟨T, hTdet, ?_, hmax⟩
  intro i
  change v (matrixColumn (columnMatrix (fun k => (b k).val)) i) ≤ 1
  rw [matrixColumn_columnMatrix]
  exact (b i).property

lemma det_updateCol_applyMatrix {d : ℕ} (T : Square d) (z : EuclideanVector d)
    (i : Fin d) :
    (T.updateCol i (fun j => applyMatrix T z j)).det = z i * T.det := by
  simpa only [applyMatrix_coordinate, smul_eq_mul, mul_comm] using
    Matrix.det_updateCol_sum T i (fun j => z j)

lemma maximal_basis_coordinate_bound {d : ℕ} {v : EuclideanVector d → ℝ}
    (hv : IsComplexNorm v) (T : Square d) (hT : T.det ≠ 0)
    (hcol : ∀ i, v (matrixColumn T i) ≤ 1)
    (hmax : ∀ S : Square d, (∀ i, v (matrixColumn S i) ≤ 1) → ‖S.det‖ ≤ ‖T.det‖)
    (z : EuclideanVector d) (i : Fin d) :
    ‖z i‖ ≤ v (applyMatrix T z) := by
  classical
  let y := applyMatrix T z
  by_cases hy : v y = 0
  · have hy0 : y = 0 := (hv.2.1 y).mp hy
    have hz : z = 0 := by
      have he := congrArg (applyMatrix T⁻¹) hy0
      simpa only [y, ← applyMatrix_mul, Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hT),
        applyMatrix_one, applyMatrix_zero] using he
    simp [hz, complexNorm_zero hv]
  · have hyp : 0 < v y := lt_of_le_of_ne (hv.1 y) (Ne.symm hy)
    let x : EuclideanVector d := ((v y)⁻¹ : ℂ) • y
    have hx : v x ≤ 1 := by
      dsimp only [x]
      rw [hv.2.2.2]
      simp [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hyp, hy]
    let S := T.updateCol i (fun j => x j)
    have hS : ∀ j, v (matrixColumn S j) ≤ 1 := by
      intro j
      dsimp only [S]
      rw [matrixColumn_updateCol]
      split_ifs with hj
      · exact hx
      · exact hcol j
    have he : S.det = (v y : ℂ)⁻¹ * (z i * T.det) := by
      change (T.updateCol i (((v y)⁻¹ : ℂ) • (fun j => y j))).det = _
      dsimp only [y]
      rw [Matrix.det_updateCol_smul, det_updateCol_applyMatrix]
    have hn := hmax S hS
    rw [he, norm_mul, norm_mul] at hn
    have hh : (v y)⁻¹ * ‖z i‖ ≤ 1 := by
      apply (mul_le_mul_iff_right₀ (norm_pos_iff.mpr hT)).mp
      simpa [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hyp,
        mul_assoc, mul_comm, mul_left_comm] using hn
    calc
      ‖z i‖ = v y * ((v y)⁻¹ * ‖z i‖) := by rw [← mul_assoc, mul_inv_cancel₀ hy, one_mul]
      _ ≤ v y * 1 := mul_le_mul_of_nonneg_left hh hyp.le
      _ = v (applyMatrix T z) := mul_one _

lemma basis_norm_upper {d : ℕ} {v : EuclideanVector d → ℝ} (hv : IsComplexNorm v)
    (T : Square d) (hcol : ∀ i, v (matrixColumn T i) ≤ 1) (z : EuclideanVector d) :
    v (applyMatrix T z) ≤ ∑ i, ‖z i‖ := by
  rw [applyMatrix_eq_sum_columns]
  calc
    v (∑ i, z i • matrixColumn T i) ≤ ∑ i, v (z i • matrixColumn T i) :=
      complexNorm_sum hv Finset.univ _
    _ ≤ ∑ i, ‖z i‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [hv.2.2.2]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hcol i) (norm_nonneg (z i))

/-- Genuine Auerbach coordinates and their Euclidean estimates. -/
lemma exists_auerbach_coordinates {d : ℕ} {v : EuclideanVector d → ℝ}
    (hv : IsComplexNorm v) (c : ℝ) (hc : 1 ≤ c)
    (hbound : ∀ x, ‖x‖ ≤ v x ∧ v x ≤ c * ‖x‖) :
    ∃ T : Square d, T.det ≠ 0 ∧ ∀ z : EuclideanVector d,
      ‖z‖ ≤ Real.sqrt (d : ℝ) * v (applyMatrix T z) ∧
      v (applyMatrix T z) ≤ Real.sqrt (d : ℝ) * ‖z‖ := by
  obtain ⟨T, hT, hcol, hmax⟩ := maximal_determinant_basis hv c hc hbound
  refine ⟨T, hT, fun z => ⟨?_, ?_⟩⟩
  · exact norm_le_sqrt_card_mul_coordinate_bound z _ (hv.1 _)
      (maximal_basis_coordinate_bound hv T hT hcol hmax z)
  · exact (basis_norm_upper hv T hcol z).trans (sum_coordinate_norms_le z)

#print axioms maximal_determinant_basis
#assert_trust kernel maximal_determinant_basis
#print axioms exists_auerbach_coordinates
#assert_trust kernel exists_auerbach_coordinates

end NLA.MF07
