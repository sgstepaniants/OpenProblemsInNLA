/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Opposite diagonal peaks and the exact one-sided second-order limit identify
weighted row and column magnitudes in every dimension.
-/
import NLA.MI04.Limit
import NLA.MI04.ScaledSymmetry

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators Topology ComplexOrder
open Filter

namespace NLA.MI04

def sumDiagonal {n : ℕ} (d : Fin n → ℝ) : Fin n ⊕ Fin n → ℝ :=
  Sum.elim d (fun j => -d j)

lemma realDiagonal_neg {n : ℕ} (d : Fin n → ℝ) :
    realDiagonal (fun j => -d j) = -realDiagonal d := by
  ext i j
  simp [realDiagonal, Matrix.diagonal]

lemma realDiagonal_sumDiagonal {n : ℕ} (d : Fin n → ℝ) :
    realDiagonal (sumDiagonal d) =
      Matrix.fromBlocks (realDiagonal d) 0 0 (-realDiagonal d) := by
  ext i j
  cases i <;> cases j <;>
    simp [realDiagonal, sumDiagonal, Matrix.diagonal, Matrix.fromBlocks]

lemma perturbedDiagonal_pencil {n : ℕ} (d : Fin n → ℝ) (X : Square n) (ε : ℝ) :
    perturbedDiagonal (sumDiagonal d) (pencil X 0) ε =
      pencil ((ε : ℂ) • X) (realDiagonal d) := by
  rw [perturbedDiagonal, realDiagonal_sumDiagonal]
  simp [pencil, completion, Matrix.fromBlocks_smul, Matrix.fromBlocks_add,
    Matrix.conjTranspose_smul]

lemma sumDiagonal_peak_left {n : ℕ} (d : Fin n → ℝ) (i : Fin n)
    (hi : d i = 1)
    (hd : ∀ j, j ≠ i → -(1 : ℝ) / 2 ≤ d j ∧ d j ≤ (1 : ℝ) / 2) :
    sumDiagonal d (Sum.inl i) = 1 ∧
      ∀ a, a ≠ Sum.inl i → sumDiagonal d a ≤ (1 : ℝ) / 2 := by
  refine ⟨hi, ?_⟩
  intro a ha
  cases a with
  | inl j =>
    exact (hd j (fun h => ha (congrArg Sum.inl h))).2
  | inr j =>
    by_cases hj : j = i
    · subst j
      norm_num [sumDiagonal, hi]
    · have h := (hd j hj).1
      change -d j ≤ (1 : ℝ) / 2
      linarith

lemma sumDiagonal_peak_right {n : ℕ} (d : Fin n → ℝ) (i : Fin n)
    (hi : d i = 1)
    (hd : ∀ j, j ≠ i → -(1 : ℝ) / 2 ≤ d j ∧ d j ≤ (1 : ℝ) / 2) :
    sumDiagonal (fun j => -d j) (Sum.inr i) = 1 ∧
      ∀ a, a ≠ Sum.inr i → sumDiagonal (fun j => -d j) a ≤ (1 : ℝ) / 2 := by
  refine ⟨by simpa [sumDiagonal] using hi, ?_⟩
  intro a ha
  cases a with
  | inl j =>
    by_cases hj : j = i
    · subst j
      norm_num [sumDiagonal, hi]
    · have h := (hd j hj).1
      change -d j ≤ (1 : ℝ) / 2
      linarith
  | inr j =>
    simpa only [sumDiagonal, Sum.elim_inr, neg_neg] using
      (hd j (fun h => ha (congrArg Sum.inr h))).2

lemma secondCoefficient_row {n : ℕ} (X : Square n) (d : Fin n → ℝ) (i : Fin n) :
    secondCoefficient (sumDiagonal d) (pencil X 0) (Sum.inl i) =
      ∑ j, Complex.normSq (X i j) / (1 + d j) := by
  simp [secondCoefficient, Fintype.sum_sum_type, sumDiagonal, pencil, completion,
    Matrix.fromBlocks, Matrix.conjTranspose_apply, Complex.star_def, sub_neg_eq_add]

lemma secondCoefficient_column {n : ℕ} (X : Square n) (d : Fin n → ℝ) (i : Fin n) :
    secondCoefficient (sumDiagonal (fun j => -d j)) (pencil X 0) (Sum.inr i) =
      ∑ j, Complex.normSq (X j i) / (1 + d j) := by
  simp [secondCoefficient, Fintype.sum_sum_type, sumDiagonal, pencil, completion,
    Matrix.fromBlocks, Matrix.conjTranspose_apply, Complex.star_def, sub_neg_eq_add]

theorem weighted_magnitude_identity {n : ℕ} (hn : 1 ≤ n) (X : Square n)
    (hX : ExtremeSymmetry X) (i : Fin n) (d : Fin n → ℝ)
    (hi : d i = 1) (hd : ∀ j, j ≠ i → -(1 : ℝ) / 2 ≤ d j ∧ d j ≤ (1 : ℝ) / 2) :
    (∑ j, Complex.normSq (X i j) / (1 + d j)) =
      ∑ j, Complex.normSq (X j i) / (1 + d j) := by
  letI : Nonempty (Fin n) := ⟨i⟩
  have hV : (pencil X 0).IsHermitian := pencil_isHermitian X 0 Matrix.isHermitian_zero
  obtain ⟨hleft, hleftgap⟩ := sumDiagonal_peak_left d i hi hd
  obtain ⟨hright, hrightgap⟩ := sumDiagonal_peak_right d i hi hd
  have haaL : pencil X 0 (Sum.inl i) (Sum.inl i) = 0 := by
    simp [pencil, completion, Matrix.fromBlocks]
  have haaR : pencil X 0 (Sum.inr i) (Sum.inr i) = 0 := by
    simp [pencil, completion, Matrix.fromBlocks]
  have hlimL := simple_peak_second_order (sumDiagonal d) (pencil X 0)
    (Sum.inl i) hleft hleftgap hV haaL
  have hlimR := simple_peak_second_order (sumDiagonal (fun j => -d j)) (pencil X 0)
    (Sum.inr i) hright hrightgap hV haaR
  have heq : (fun ε : ℝ =>
      (topValue (perturbedDiagonal (sumDiagonal d) (pencil X 0) ε) - 1) / ε ^ 2)
      =ᶠ[𝓝[>] (0 : ℝ)] (fun ε : ℝ =>
      (topValue (perturbedDiagonal (sumDiagonal (fun j => -d j))
        (pencil X 0) ε) - 1) / ε ^ 2) := by
    filter_upwards [eventually_mem_nhdsWithin] with ε hε
    have hscaled : ExtremeSymmetry ((ε : ℂ) • X) :=
      extreme_symmetry_positive_scale hn X hX ε hε
    have h := hscaled (realDiagonal d) (realDiagonal_isHermitian d)
    have hs := topValue_pencil_neg_diag hn ((ε : ℂ) • X) (realDiagonal d)
    rw [perturbedDiagonal_pencil, perturbedDiagonal_pencil, realDiagonal_neg]
    exact congrArg (fun x : ℝ => (x - 1) / ε ^ 2) (h.trans hs.symm)
  have hcoeff := tendsto_nhds_unique (hlimL.congr' heq) hlimR
  simpa only [secondCoefficient_row, secondCoefficient_column] using hcoeff

#print axioms weighted_magnitude_identity
#assert_trust kernel weighted_magnitude_identity

end NLA.MI04
