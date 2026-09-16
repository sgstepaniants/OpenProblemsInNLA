/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

An explicit unitary sign flip exchanges the two pencil extrema. A scalar
boundary shift gives an actual positive completion of the original X.
-/
import NLA.MI04.Unitary
import NLA.MI04.Coordinates

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04

section Scalars
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma topValue_zero : topValue (0 : CMatrix ι) = 0 := by
  obtain ⟨u, _, he, _⟩ := topValue_attained (0 : CMatrix ι)
  simpa only [realQuadratic_zero] using he.symm

lemma topValue_real_scalar (c : ℝ) :
    topValue ((c : ℂ) • (1 : CMatrix ι)) = c := by
  simpa only [add_zero, topValue_zero] using
    shifted_topValue (0 : CMatrix ι) Matrix.isHermitian_zero c

lemma positive_real_scalar (c : ℝ) (hc : 0 ≤ c) :
    ((c : ℂ) • (1 : CMatrix ι)).PosSemidef := by
  apply (positive_quadratic_iff _).mpr
  refine ⟨hermitian_real_smul 1 Matrix.isHermitian_one c, ?_⟩
  intro v
  rw [realQuadratic_smul_matrix, realQuadratic_one]
  exact mul_nonneg hc (sq_nonneg _)

lemma spectralNorm_real_scalar (c : ℝ) (hc : 0 ≤ c) :
    spectralNorm ((c : ℂ) • (1 : CMatrix ι)) = c := by
  rw [positive_norm_eq_top _ (positive_real_scalar c hc), topValue_real_scalar]

end Scalars

def blockSign (n : ℕ) : Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
  refine ⟨Matrix.fromBlocks (1 : Square n) 0 0 (-1), ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.fromBlocks_conjTranspose]
  simp [Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

lemma signFlip_negative_pencil {n : ℕ} (X T : Square n) :
    unitarySimilarity (-pencil X T) (blockSign n) = pencil X (-T) := by
  change (Matrix.fromBlocks (1 : Square n) 0 0 (-1)).conjTranspose *
      (-Matrix.fromBlocks T X X.conjTranspose (-T)) *
      Matrix.fromBlocks (1 : Square n) 0 0 (-1) =
    Matrix.fromBlocks (-T) X X.conjTranspose (-(-T))
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_multiply]

lemma topValue_pencil_neg_diag {n : ℕ} (hn : 1 ≤ n) (X T : Square n) :
    topValue (pencil X (-T)) = topValue (-pencil X T) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rw [← signFlip_negative_pencil]
  exact topValue_unitarySimilarity _ _

lemma negative_pencil_top_nonneg {n : ℕ} (hn : 1 ≤ n) (X T : Square n) :
    0 ≤ topValue (-pencil X T) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let a : Fin n := ⟨0, by omega⟩
  have hleft := realQuadratic_le_top_of_unit (-pencil X T)
    (coordinateUnit (Sum.inl a)) (coordinateUnit_norm _)
  have hright := realQuadratic_le_top_of_unit (-pencil X T)
    (coordinateUnit (Sum.inr a)) (coordinateUnit_norm _)
  rw [realQuadratic_coordinateUnit] at hleft hright
  have hleft' : -(T a a).re ≤ topValue (-pencil X T) := by
    simpa [pencil, completion, Matrix.fromBlocks] using hleft
  have hright' : (T a a).re ≤ topValue (-pencil X T) := by
    simpa [pencil, completion, Matrix.fromBlocks] using hright
  linarith

lemma completion_boundary_shift {n : ℕ} (X T : Square n) (c : ℝ) :
    completion ((c : ℂ) • 1 + T) X ((c : ℂ) • 1 - T) =
      (c : ℂ) • (1 : Block n) + pencil X T := by
  ext i j
  cases i <;> cases j <;>
    simp [completion, pencil, Matrix.fromBlocks, Matrix.one_apply, sub_eq_add_neg]

lemma opposite_diagonal_sum {n : ℕ} (T : Square n) (c : ℝ) :
    ((c : ℂ) • 1 + T) + ((c : ℂ) • 1 - T) =
      ((2 * c : ℝ) : ℂ) • (1 : Square n) := by
  calc
    ((c : ℂ) • 1 + T) + ((c : ℂ) • 1 - T) =
        (c : ℂ) • 1 + (c : ℂ) • (1 : Square n) := by abel
    _ = ((2 * c : ℝ) : ℂ) • (1 : Square n) := by
      rw [← add_smul]
      congr 1
      push_cast
      ring

lemma universal_pencil_top_le_negative {n : ℕ} (hn : 1 ≤ n) (X : Square n)
    (hX : UniversalBlockNorm X) (T : Square n) (hT : T.IsHermitian) :
    topValue (pencil X T) ≤ topValue (-pencil X T) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let c : ℝ := topValue (-pencil X T)
  have hc : 0 ≤ c := negative_pencil_top_nonneg hn X T
  have hK := pencil_isHermitian X T hT
  have hp : ((c : ℂ) • (1 : Block n) + pencil X T).PosSemidef := by
    simpa only [sub_neg_eq_add] using
      (scalar_order_iff_top (-pencil X T) hK.neg c).mpr (le_refl c)
  have hA : ((c : ℂ) • (1 : Square n) + T).IsHermitian :=
    (hermitian_real_smul 1 Matrix.isHermitian_one c).add hT
  have hB : ((c : ℂ) • (1 : Square n) - T).IsHermitian :=
    (hermitian_real_smul 1 Matrix.isHermitian_one c).sub hT
  have hp' : (completion ((c : ℂ) • 1 + T) X ((c : ℂ) • 1 - T)).PosSemidef := by
    rw [completion_boundary_shift]
    exact hp
  have h := hX ((c : ℂ) • 1 + T) ((c : ℂ) • 1 - T) hA hB hp'
  rw [completion_boundary_shift, positive_norm_eq_top _ hp,
    shifted_topValue _ hK c, opposite_diagonal_sum,
    spectralNorm_real_scalar (2 * c) (mul_nonneg (by norm_num) hc)] at h
  change topValue (pencil X T) ≤ c
  linarith

theorem universal_to_extreme_symmetry {n : ℕ} (hn : 1 ≤ n) (X : Square n)
    (hX : UniversalBlockNorm X) : ExtremeSymmetry X := by
  intro T hT
  apply le_antisymm (universal_pencil_top_le_negative hn X hX T hT)
  have h := universal_pencil_top_le_negative hn X hX (-T) hT.neg
  rw [topValue_pencil_neg_diag hn X T] at h
  have he := topValue_pencil_neg_diag hn X (-T)
  simp only [neg_neg] at he
  rw [← he] at h
  exact h

#print axioms universal_to_extreme_symmetry
#assert_trust kernel universal_to_extreme_symmetry

end NLA.MI04
