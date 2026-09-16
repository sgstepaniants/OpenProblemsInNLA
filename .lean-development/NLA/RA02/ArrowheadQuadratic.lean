/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

A symbolic complex sum of squares proves PSD of every active true state and
positive definiteness of the full arrowhead. No determinant enumeration.
-/
import NLA.RA02.ArrowheadEntries
import Mathlib.Data.Complex.BigOperators

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

def stateEnergy (r : ℕ) (U : Finset (Fin r)) (x : Fin (r + 1) → ℂ) : ℝ :=
  (∑ i ∈ U, diagonalWeight r i.val *
    Complex.normSq (x i.castSucc + (couplingWeight r i.val : ℂ) * x (Fin.last r))) +
  scaleParameter r ^ r * Complex.normSq (x (Fin.last r))

lemma state_true_mulVec_ordinary (r : ℕ) (U : Finset (Fin r))
    (x : Fin (r + 1) → ℂ) (i : Fin r) :
    (arrowheadState r U true *ᵥ x) i.castSucc =
      if i ∈ U then (diagonalWeight r i.val : ℂ) *
        (x i.castSucc + (couplingWeight r i.val : ℂ) * x (Fin.last r)) else 0 := by
  rw [Matrix.mulVec_apply, dotProduct, Fin.sum_univ_castSucc]
  by_cases hi : i ∈ U <;> simp [hi, ite_mul, Complex.ofReal_mul] <;> ring

lemma state_true_mulVec_last (r : ℕ) (U : Finset (Fin r))
    (x : Fin (r + 1) → ℂ) :
    (arrowheadState r U true *ᵥ x) (Fin.last r) =
      (∑ i ∈ U, ((diagonalWeight r i.val * couplingWeight r i.val : ℝ) : ℂ) *
        x i.castSucc) + (cornerValue r U : ℂ) * x (Fin.last r) := by
  rw [Matrix.mulVec_apply, dotProduct, Fin.sum_univ_castSucc]
  simp [ite_mul]

lemma complex_energy_term (d a : ℝ) (x z : ℂ) :
    star x * ((d : ℂ) * (x + (a : ℂ) * z)) +
      star z * ((d : ℂ) * (a : ℂ) * x) +
      ((d * a ^ 2 : ℝ) : ℂ) * star z * z =
      ((d * Complex.normSq (x + (a : ℂ) * z) : ℝ) : ℂ) := by
  simp only [Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.normSq_eq_conj_mul_self, Complex.star_def, map_add, map_mul,
    Complex.conj_ofReal]
  ring

lemma state_true_complex_energy (r : ℕ) (U : Finset (Fin r))
    (x : Fin (r + 1) → ℂ) :
    star x ⬝ᵥ (arrowheadState r U true *ᵥ x) = (stateEnergy r U x : ℂ) := by
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp only [Pi.star_apply, state_true_mulVec_ordinary, state_true_mulVec_last]
  simp only [mul_ite, mul_zero, Finset.sum_ite_mem_eq]
  calc
    (∑ i ∈ U, star (x i.castSucc) * ((diagonalWeight r i.val : ℂ) *
        (x i.castSucc + (couplingWeight r i.val : ℂ) * x (Fin.last r)))) +
        star (x (Fin.last r)) *
          ((∑ i ∈ U, ((diagonalWeight r i.val * couplingWeight r i.val : ℝ) : ℂ) *
            x i.castSucc) + (cornerValue r U : ℂ) * x (Fin.last r)) =
        (∑ i ∈ U,
          star (x i.castSucc) * ((diagonalWeight r i.val : ℂ) *
            (x i.castSucc + (couplingWeight r i.val : ℂ) * x (Fin.last r))) +
          star (x (Fin.last r)) * ((diagonalWeight r i.val : ℂ) *
            (couplingWeight r i.val : ℂ) * x i.castSucc) +
          ((diagonalWeight r i.val * couplingWeight r i.val ^ 2 : ℝ) : ℂ) *
            star (x (Fin.last r)) * x (Fin.last r)) +
        ((scaleParameter r ^ r : ℝ) : ℂ) * star (x (Fin.last r)) * x (Fin.last r) := by
      simp only [cornerValue, Complex.ofReal_add, Complex.ofReal_sum,
        Complex.ofReal_mul, Complex.ofReal_pow, Finset.sum_add_distrib,
        mul_add, add_mul, Finset.mul_sum, Finset.sum_mul,
        mul_assoc, mul_comm, mul_left_comm]
      ring
    _ = (∑ i ∈ U,
          ((diagonalWeight r i.val * Complex.normSq
            (x i.castSucc + (couplingWeight r i.val : ℂ) * x (Fin.last r)) : ℝ) : ℂ)) +
        ((scaleParameter r ^ r * Complex.normSq (x (Fin.last r)) : ℝ) : ℂ) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i _
        exact complex_energy_term _ _ _ _
      · rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
        simp only [Complex.star_def]
        ring
    _ = (stateEnergy r U x : ℂ) := by
      simp only [stateEnergy, Complex.ofReal_add, Complex.ofReal_sum]

lemma stateEnergy_nonneg (r : ℕ) (U : Finset (Fin r)) (x : Fin (r + 1) → ℂ) :
    0 ≤ stateEnergy r U x := by
  exact add_nonneg
    (Finset.sum_nonneg fun i _ => mul_nonneg (diagonalWeight_pos r i.val).le
      (Complex.normSq_nonneg _))
    (mul_nonneg (pow_pos (scaleParameter_pos r) r).le (Complex.normSq_nonneg _))

lemma state_true_posSemidef (r : ℕ) (U : Finset (Fin r)) :
    (arrowheadState r U true).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (state_true_isHermitian r U)
  intro x
  rw [state_true_complex_energy]
  exact Complex.zero_le_real.mpr (stateEnergy_nonneg r U x)

lemma stateEnergy_univ_pos (r : ℕ) (x : Fin (r + 1) → ℂ) (hx : x ≠ 0) :
    0 < stateEnergy r Finset.univ x := by
  classical
  have he : 0 < scaleParameter r ^ r := pow_pos (scaleParameter_pos r) r
  have hsum : 0 ≤ ∑ i : Fin r, diagonalWeight r i.val *
      Complex.normSq (x i.castSucc + (couplingWeight r i.val : ℂ) * x (Fin.last r)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (diagonalWeight_pos r i.val).le
      (Complex.normSq_nonneg _)
  by_cases hz : x (Fin.last r) = 0
  · have hxord : ∃ i : Fin r, x i.castSucc ≠ 0 := by
      by_contra h
      push_neg at h
      apply hx
      funext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · exact hz
      · exact h i
    obtain ⟨i, hi⟩ := hxord
    have hterm : 0 < diagonalWeight r i.val *
        Complex.normSq (x i.castSucc + (couplingWeight r i.val : ℂ) * x (Fin.last r)) := by
      apply mul_pos (diagonalWeight_pos r i.val)
      apply Complex.normSq_pos.mpr
      simpa only [hz, mul_zero, add_zero] using hi
    have hspos := Finset.sum_pos'
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin r))) =>
        mul_nonneg (diagonalWeight_pos r j.val).le
          (Complex.normSq_nonneg
            (x j.castSucc + (couplingWeight r j.val : ℂ) * x (Fin.last r))))
      ⟨i, Finset.mem_univ i, hterm⟩
    simpa [stateEnergy, hz] using hspos
  · exact add_pos_of_nonneg_of_pos hsum (mul_pos he (Complex.normSq_pos.mpr hz))

theorem arrowhead_quadratic (r : ℕ) (x : Fin (r + 1) → ℂ) :
    quadraticValue (arrowhead r) x =
      (∑ i : Fin r, diagonalWeight r i.val *
        Complex.normSq (x i.castSucc + (couplingWeight r i.val : ℂ) * x (Fin.last r))) +
      scaleParameter r ^ r * Complex.normSq (x (Fin.last r)) := by
  unfold quadraticValue arrowhead
  rw [state_true_complex_energy]
  simp [stateEnergy]

theorem arrowhead_positive_definite (r : ℕ) (hr : 1 ≤ r) :
    (arrowhead r).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (state_true_isHermitian r Finset.univ)
  intro x hx
  change 0 < star x ⬝ᵥ (arrowheadState r Finset.univ true *ᵥ x)
  rw [state_true_complex_energy]
  exact Complex.zero_lt_real.mpr (stateEnergy_univ_pos r x hx)

#print axioms state_true_complex_energy
#assert_trust kernel state_true_complex_energy
#print axioms state_true_posSemidef
#assert_trust kernel state_true_posSemidef
#print axioms arrowhead_quadratic
#assert_trust kernel arrowhead_quadratic
#print axioms arrowhead_positive_definite
#assert_trust kernel arrowhead_positive_definite

end
end NLA.RA02
