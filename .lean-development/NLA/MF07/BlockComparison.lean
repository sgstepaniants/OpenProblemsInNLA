/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original triangular comparison:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Block triangularity is the actual entry condition from the frozen definitions.
Diagonal damping is applied to complete products, including the empty product.
-/
import NLA.MF07.RoundedNorm
import NLA.MF07.TriangularDamping
import NLA.MF07.Interspersed

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators

noncomputable section
namespace NLA.MF07

lemma spectralNorm_le_card_mul_entry_bound {d : ℕ} (A : Square d) (b : ℝ)
    (hb : 0 ≤ b) (hA : ∀ i j, ‖A i j‖ ≤ b) : spectralNorm A ≤ (d : ℝ) * b := by
  apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A).opNorm_le_bound (by positivity)
  intro x
  have hx : 0 ≤ ∑ j, ‖x j‖ := Finset.sum_nonneg fun j _ => norm_nonneg (x j)
  have hrow : ∀ i, ‖applyMatrix A x i‖ ≤ b * ∑ j, ‖x j‖ := by
    intro i
    rw [applyMatrix_coordinate]
    calc
      ‖∑ j, A i j * x j‖ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
      _ ≤ ∑ j, b * ‖x j‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg (x j))
      _ = b * ∑ j, ‖x j‖ := (Finset.mul_sum _ _ _).symm
  calc
    ‖applyMatrix A x‖ ≤ Real.sqrt (d : ℝ) * (b * ∑ j, ‖x j‖) :=
      norm_le_sqrt_card_mul_coordinate_bound _ _ (mul_nonneg hb hx) hrow
    _ ≤ Real.sqrt (d : ℝ) * (b * (Real.sqrt (d : ℝ) * ‖x‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (sum_coordinate_norms_le x) hb) (Real.sqrt_nonneg _)
    _ = ((d : ℝ) * b) * ‖x‖ := by
      have hs := Real.mul_self_sqrt (Nat.cast_nonneg d)
      calc
        _ = (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) * b * ‖x‖ := by ring
        _ = _ := by rw [hs]

lemma spectralNorm_product_of_norm {d : ℕ} (M : Set (Square d))
    (C : Square d → Square d) (w : EuclideanVector d → ℝ) (K u : ℝ)
    (hK : 0 ≤ K) (hu : 0 ≤ u)
    (hb : ∀ x, ‖x‖ ≤ w x ∧ w x ≤ K * ‖x‖)
    (hC : ∀ A ∈ M, ∀ x, w (applyMatrix (C A) x) ≤ u * w x)
    (z : List (Square d)) (hz : WordIn M z) :
    spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length := by
  apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) _).opNorm_le_bound (by positivity)
  intro x
  calc
    ‖applyMatrix (matrixProduct (z.map C)) x‖ ≤ w (applyMatrix (matrixProduct (z.map C)) x) :=
      (hb _).1
    _ ≤ u ^ z.length * w x := norm_product_from_generator M C w u hu hC z hz x
    _ ≤ u ^ z.length * (K * ‖x‖) := mul_le_mul_of_nonneg_left (hb x).2 (pow_nonneg hu _)
    _ = (K * u ^ z.length) * ‖x‖ := by ring

lemma lowerForWeights_one {d : ℕ} (h : Fin d → ℝ) : LowerForWeights h (1 : Square d) := by
  intro i j hij
  have hne : i ≠ j := by rintro rfl; exact (lt_irrefl _ hij)
  simp [Matrix.one_apply, hne]

lemma lowerForWeights_mul {d : ℕ} (h : Fin d → ℝ) {X Y : Square d}
    (hX : LowerForWeights h X) (hY : LowerForWeights h Y) : LowerForWeights h (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : h k < h i
  · rw [hX i k hk, zero_mul]
  · rw [hY k j (hij.trans_le (le_of_not_gt hk)), mul_zero]

lemma lowerForWeights_product {d : ℕ} (h : Fin d → ℝ) (z : List (Square d))
    (hz : ∀ A ∈ z, LowerForWeights h A) : LowerForWeights h (matrixProduct z) := by
  induction z with
  | nil => simpa using lowerForWeights_one h
  | cons A z ih =>
      rw [matrixProduct_cons]
      exact lowerForWeights_mul h (ih fun B hB => hz B (List.mem_cons_of_mem A hB))
        (hz A (List.mem_cons_self _ _))

lemma diagonalDamping_one {d : ℕ} (h : Fin d → ℝ) (hh : ∀ i, h i ≠ 0) :
    diagonalDamping h (1 : Square d) = 1 := by
  simpa only [diagonalDamping, mul_one] using (diagonal_inverse h hh).1

lemma diagonalDamping_mul {d : ℕ} (h : Fin d → ℝ) (hh : ∀ i, h i ≠ 0)
    (X Y : Square d) :
    diagonalDamping h (X * Y) = diagonalDamping h X * diagonalDamping h Y := by
  symm
  calc
    diagonalDamping h X * diagonalDamping h Y =
        diagonalWeights h * X * (inverseDiagonalWeights h * diagonalWeights h) *
          Y * inverseDiagonalWeights h := by
      dsimp [diagonalDamping]
      noncomm_ring
    _ = diagonalDamping h (X * Y) := by
      rw [(diagonal_inverse h hh).2]
      dsimp [diagonalDamping]
      noncomm_ring

lemma diagonalDamping_product {d : ℕ} (h : Fin d → ℝ) (hh : ∀ i, h i ≠ 0)
    (z : List (Square d)) :
    matrixProduct (z.map (diagonalDamping h)) = diagonalDamping h (matrixProduct z) := by
  induction z with
  | nil => simp [diagonalDamping_one h hh]
  | cons A z ih =>
      simp only [List.map_cons, matrixProduct_cons, ih, diagonalDamping_mul h hh]

lemma damped_lower_product_bound {d : ℕ} (h : Fin d → ℝ) (hh : Antitone h)
    (hpos : ∀ i, 0 < h i) (z : List (Square d)) (hz : ∀ A ∈ z, LowerForWeights h A) :
    spectralNorm (matrixProduct (z.map (diagonalDamping h))) ≤ spectralNorm (matrixProduct z) := by
  rw [diagonalDamping_product h (fun i => (hpos i).ne')]
  exact triangular_damping h hh hpos _ (lowerForWeights_product h z hz)

/-- The strictly upper weight-block part; equal-weight blocks remain intact. -/
def upperWeightPart {d : ℕ} (h : Fin d → ℝ) (X : Square d) : Square d :=
  fun i j => if h j < h i then X i j else 0

lemma subtract_upperWeightPart_lower {d : ℕ} (h : Fin d → ℝ) (X : Square d) :
    LowerForWeights h (X - upperWeightPart h X) := by
  intro i j hij
  simp [upperWeightPart, hij]

lemma upperWeightPart_entry_bound {d : ℕ} (h : Fin d → ℝ) (X : Square d) (b : ℝ)
    (hb : 0 ≤ b) (hX : ∀ i j, h j < h i → ‖X i j‖ ≤ b) :
    ∀ i j, ‖upperWeightPart h X i j‖ ≤ b := by
  intro i j
  by_cases hij : h j < h i
  · simpa only [upperWeightPart, if_pos hij] using hX i j hij
  · simpa only [upperWeightPart, if_neg hij, norm_zero] using hb

#print axioms spectralNorm_le_card_mul_entry_bound
#assert_trust kernel spectralNorm_le_card_mul_entry_bound
#print axioms damped_lower_product_bound
#assert_trust kernel damped_lower_product_bound

end NLA.MF07
