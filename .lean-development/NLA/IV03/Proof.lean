/- Copyright (c) 2026 Sidney Holden. Released under Apache 2.0.
AI-assisted proof development for Matthew J. Colbrook's IV-03 argument.
Checked weighted Z-matrix foundations. No Challenge is imported. -/
import NLA.IV03.Definitions
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Matrix
namespace NLA.IV03

lemma inverseM_diagonal_product {n : ℕ} {A : Mat n} (hA : IsInverseM A) (i : Fin n) :
    1 ≤ A i i * A⁻¹ i i := by
  have he := congrFun (congrFun (Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.1)) i) i
  simp only [Matrix.mul_apply, Matrix.one_apply_eq] at he
  have hoff : ∑ j ∈ Finset.univ.erase i, A i j * A⁻¹ j i ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    exact mul_nonpos_of_nonneg_of_nonpos (hA.2.1 i j)
      (hA.2.2 j i (Finset.mem_erase.mp hj).1)
  have hs := Finset.sum_erase_add (s := Finset.univ)
    (f := fun j => A i j * A⁻¹ j i) (Finset.mem_univ i)
  linarith

lemma inverseM_diagonal_pos {n : ℕ} {A : Mat n} (hA : IsInverseM A) (i : Fin n) :
    0 < A i i ∧ 0 < A⁻¹ i i := by
  have hp := inverseM_diagonal_product hA i
  have ha := hA.2.1 i i
  have hp' : 0 < A i i * A⁻¹ i i := lt_of_lt_of_le zero_lt_one hp
  exact ⟨lt_of_le_of_ne ha (by intro h; simp [← h] at hp'),
    (mul_pos_iff_of_pos_left (lt_of_le_of_ne ha (by intro h; simp [← h] at hp'))).mp hp'⟩

/-- The source's positive weight is the row-sum vector of A=B⁻¹. -/
lemma inverseM_positive_weight {n : ℕ} {A : Mat n} (hA : IsInverseM A) :
    ∃ w : Fin n → ℝ, (∀ i, 0 < w i) ∧ A⁻¹ *ᵥ w = fun _ => 1 := by
  let w : Fin n → ℝ := A *ᵥ (fun _ => 1)
  refine ⟨w, ?_, ?_⟩
  · intro i
    have hs : A i i ≤ ∑ j, A i j :=
      Finset.single_le_sum (fun j _ => hA.2.1 i j) (Finset.mem_univ i)
    simpa [w, Matrix.mulVec, dotProduct] using (inverseM_diagonal_pos hA i).1.trans_le hs
  · dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.1)]
    simp

/-- A weighted maximum principle for every real Z-matrix with a strict positive
supersolution. It will establish nonnegativity of the genuine inverse. -/
lemma zMatrix_maximum_principle {n : ℕ} (B : Mat n) (w y : Fin n → ℝ)
    (hZ : ∀ i j, i ≠ j → B i j ≤ 0) (hw : ∀ i, 0 < w i)
    (hBw : ∀ i, 0 < (B *ᵥ w) i) (hBy : ∀ i, 0 ≤ (B *ᵥ y) i) :
    ∀ i, 0 ≤ y i := by
  intro a
  by_contra ha
  have hya : y a < 0 := lt_of_not_ge ha
  obtain ⟨i, _hi, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun j => y j / w j) ⟨a, Finset.mem_univ a⟩
  let r : ℝ := y i / w i
  have hr : r < 0 := lt_of_le_of_lt (hmin a (Finset.mem_univ a))
    (div_neg_of_neg_of_pos hya (hw a))
  have hyw : ∀ j, r * w j ≤ y j := by
    intro j
    exact (le_div_iff₀ (hw j)).mp (hmin j (Finset.mem_univ j))
  have hei : r * w i = y i := div_mul_cancel₀ _ (ne_of_gt (hw i))
  have hsum : (B *ᵥ y) i ≤ r * (B *ᵥ w) i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _hj
    by_cases hji : j = i
    · subst j
      rw [← hei]
      ring_nf
      exact le_rfl
    · have ht := mul_le_mul_of_nonpos_left (hyw j) (hZ i j (Ne.symm hji))
      nlinarith
  have hn : r * (B *ᵥ w) i < 0 := mul_neg_of_neg_of_pos hr (hBw i)
  linarith [hBy i]

lemma zMatrix_isUnit {n : ℕ} (B : Mat n) (w : Fin n → ℝ)
    (hZ : ∀ i j, i ≠ j → B i j ≤ 0) (hw : ∀ i, 0 < w i)
    (hBw : ∀ i, 0 < (B *ᵥ w) i) : IsUnit B := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have h0 : B *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  have h1 : B *ᵥ (y - x) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
  have hp := zMatrix_maximum_principle B w (x - y) hZ hw hBw (by simp [h0])
  have hn := zMatrix_maximum_principle B w (y - x) hZ hw hBw (by simp [h1])
  funext i
  have hpi := hp i
  have hni := hn i
  change 0 ≤ x i - y i at hpi
  change 0 ≤ y i - x i at hni
  linarith

lemma zMatrix_inverse_nonnegative {n : ℕ} (B : Mat n) (w : Fin n → ℝ)
    (hZ : ∀ i j, i ≠ j → B i j ≤ 0) (hw : ∀ i, 0 < w i)
    (hBw : ∀ i, 0 < (B *ᵥ w) i) : ∀ i j, 0 ≤ B⁻¹ i j := by
  have hu := zMatrix_isUnit B w hZ hw hBw
  intro i j
  have he : B *ᵥ (B⁻¹ *ᵥ Pi.single j 1) = Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv B
      ((Matrix.isUnit_iff_isUnit_det B).mp hu)]
    exact Matrix.one_mulVec (Pi.single j 1)
  have hh := zMatrix_maximum_principle B w (B⁻¹ *ᵥ Pi.single j 1) hZ hw hBw
    (by intro k; rw [he]; simp [Pi.single_apply]; split_ifs <;> norm_num)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hh i

/-- Positive determinant follows through a nonsingular homotopy, so no spectral
radius theorem or determinant-sign assumption is introduced. -/
lemma zMatrix_det_pos {n : ℕ} (B : Mat n) (w : Fin n → ℝ)
    (hZ : ∀ i j, i ≠ j → B i j ≤ 0) (hw : ∀ i, 0 < w i)
    (hBw : ∀ i, 0 < (B *ᵥ w) i) : 0 < B.det := by
  let H : ℝ → Mat n := fun t => (1 - t) • (1 : Mat n) + t • B
  have hunit : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (H t) := by
    intro t ht
    apply zMatrix_isUnit (H t) w
    · intro i j hij
      have hz := hZ i j hij
      simpa [H, Matrix.one_apply, hij] using mul_nonpos_of_nonneg_of_nonpos ht.1 hz
    · exact hw
    · intro i
      have he : (H t *ᵥ w) i = (1 - t) * w i + t * (B *ᵥ w) i := by
        simp [H, Matrix.add_mulVec, Matrix.smul_mulVec]
      rw [he]
      rcases lt_or_eq_of_le ht.2 with hlt | rfl
      · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) (hw i))
          (mul_nonneg ht.1 (hBw i).le)
      · simpa using hBw i
  have hc : Continuous (fun t => (H t).det) := by
    apply Continuous.matrix_det
    dsimp [H]
    fun_prop
  by_contra hn
  have hm : (H 1).det ≤ (0 : ℝ) := by simpa [H] using le_of_not_gt hn
  have h0 : (0 : ℝ) ≤ (H 0).det := by simp [H]
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1)
    hc.continuousOn ⟨hm, h0⟩
  exact ((Matrix.isUnit_iff_isUnit_det (H t)).mp (hunit t ht)).ne_zero he

/-- Restricting a Z-matrix to any principal index subset can only increase the
weighted row sums, since all removed contributions are nonpositive. -/
lemma zMatrix_principal_weight {m n : ℕ} (B : Mat n) (w : Fin n → ℝ)
    (e : Fin m ↪ Fin n) (hZ : ∀ i j, i ≠ j → B i j ≤ 0)
    (hw : ∀ i, 0 < w i) (hBw : ∀ i, 0 < (B *ᵥ w) i) :
    ∀ i, 0 < (B.submatrix e e *ᵥ (fun j => w (e j))) i := by
  intro i
  have hc := Finset.sum_le_sum_of_subset_of_nonneg
    (f := fun j => -(B (e i) j * w j))
    (Finset.subset_univ (Finset.univ.map e)) (by
      intro j _hj hn
      apply neg_nonneg.mpr
      apply mul_nonpos_of_nonpos_of_nonneg
      · apply hZ
        intro he
        apply hn
        exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, he⟩
      · exact (hw j).le)
  simp only [Finset.sum_neg_distrib, Finset.sum_map] at hc
  have hp := hBw (e i)
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply] at hp ⊢
  linarith

lemma zMatrix_principal_properties {m n : ℕ} (B : Mat n) (w : Fin n → ℝ)
    (e : Fin m ↪ Fin n) (hZ : ∀ i j, i ≠ j → B i j ≤ 0)
    (hw : ∀ i, 0 < w i) (hBw : ∀ i, 0 < (B *ᵥ w) i) :
    IsUnit (B.submatrix e e) ∧ 0 < (B.submatrix e e).det ∧
      ∀ i j, 0 ≤ (B.submatrix e e)⁻¹ i j := by
  have hz : ∀ i j : Fin m, i ≠ j → B.submatrix e e i j ≤ 0 := by
    intro i j hij
    exact hZ (e i) (e j) (fun he => hij (e.injective he))
  have hwp : ∀ i : Fin m, 0 < w (e i) := fun i => hw (e i)
  have hbp := zMatrix_principal_weight B w e hZ hw hBw
  exact ⟨zMatrix_isUnit _ _ hz hwp hbp, zMatrix_det_pos _ _ hz hwp hbp,
    zMatrix_inverse_nonnegative _ _ hz hwp hbp⟩

lemma inverseM_det_pos {n : ℕ} {A : Mat n} (hA : IsInverseM A) : 0 < A.det := by
  obtain ⟨w, hw, he⟩ := inverseM_positive_weight hA
  have hp := zMatrix_det_pos A⁻¹ w hA.2.2 hw (by simp [he])
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv] at hp
  exact inv_pos.mp hp

/-- Principal M-matrix closure for B=A⁻¹, including the empty principal matrix. -/
lemma inverseM_inverse_principal {m n : ℕ} {A : Mat n} (hA : IsInverseM A)
    (e : Fin m ↪ Fin n) :
    IsUnit ((A⁻¹).submatrix e e) ∧ 0 < ((A⁻¹).submatrix e e).det ∧
      ∀ i j, 0 ≤ ((A⁻¹).submatrix e e)⁻¹ i j := by
  obtain ⟨w, hw, he⟩ := inverseM_positive_weight hA
  exact zMatrix_principal_properties A⁻¹ w e hA.2.2 hw (by simp [he])

/-- The exact three-index contradiction used in the negative-determinant branch
of the source's adjugate completion lemma. The principal-minor transfer from a
larger matrix is a separate obligation, not an assumed conclusion here. -/
lemma threeByThree_negative_minors_det_pos (B : Mat 3)
    (hd : ∀ i, B i i < 0) (ho : ∀ i j, i ≠ j → 0 ≤ B i j)
    (hm01 : B 0 0 * B 1 1 - B 0 1 * B 1 0 < 0)
    (hm02 : B 0 0 * B 2 2 - B 0 2 * B 2 0 < 0)
    (hm12 : B 1 1 * B 2 2 - B 1 2 * B 2 1 < 0) : 0 < B.det := by
  have hp01 := mul_pos_of_neg_of_neg hm01 (hd 2)
  have hp02 := mul_pos_of_neg_of_neg hm02 (hd 1)
  have hp12 := mul_pos_of_neg_of_neg hm12 (hd 0)
  have hc1 : 0 ≤ B 0 1 * B 1 2 * B 2 0 :=
    mul_nonneg (mul_nonneg (ho 0 1 (by decide)) (ho 1 2 (by decide)))
      (ho 2 0 (by decide))
  have hc2 : 0 ≤ B 0 2 * B 1 0 * B 2 1 :=
    mul_nonneg (mul_nonneg (ho 0 2 (by decide)) (ho 1 0 (by decide)))
      (ho 2 1 (by decide))
  have hn : B 0 0 * B 1 1 * B 2 2 < 0 :=
    mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (hd 0) (hd 1)) (hd 2)
  rw [Matrix.det_fin_three]
  nlinarith

/-- The Schur complement of a Z-matrix is again Z when the eliminated block
has a nonnegative inverse. This entrywise sign bridge is independent of the
separate block-inverse and principal-minor identities. -/
lemma zMatrix_schur_offdiagonal {m n : ℕ} (A : Mat m)
    (B : Matrix (Fin m) (Fin n) ℝ) (C : Matrix (Fin n) (Fin m) ℝ) (D : Mat n)
    (hA : ∀ i j, i ≠ j → A i j ≤ 0)
    (hB : ∀ i j, B i j ≤ 0) (hC : ∀ i j, C i j ≤ 0)
    (hD : ∀ i j, 0 ≤ D⁻¹ i j) :
    ∀ i j, i ≠ j → (A - B * D⁻¹ * C) i j ≤ 0 := by
  intro i j hij
  have hp : 0 ≤ (B * D⁻¹ * C) i j := by
    rw [Matrix.mul_apply]
    apply Finset.sum_nonneg
    intro k _hk
    apply mul_nonneg_of_nonpos_of_nonpos
    · rw [Matrix.mul_apply]
      apply Finset.sum_nonpos
      intro l _hl
      exact mul_nonpos_of_nonpos_of_nonneg (hB i l) (hD l k)
    · exact hC k j
  change A i j - (B * D⁻¹ * C) i j ≤ 0
  linarith [hA i j hij]

end NLA.IV03
