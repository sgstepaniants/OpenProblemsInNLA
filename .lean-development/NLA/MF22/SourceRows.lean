/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Finite sums identify every row of the literal scaled Toeplitz matrix with
the source stencil, including the boundary rows by exact zero extension.
-/
import NLA.MF22.Coordinates
import Mathlib.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open scoped BigOperators

noncomputable section

def stencilBlock (ρ : ℝ) (k : ℤ) : Square 2 :=
  (if k = -1 then !![coefficientA ρ, 0; coefficientB ρ, 0] else 0) +
  (if k = 0 then !![-24 * (ρ : ℂ), coefficientB ρ;
    96 * Complex.I, coefficientD ρ] else 0) +
  (if k = 1 then !![coefficientF ρ, 96 * Complex.I;
    coefficientC ρ, 24 * (ρ : ℂ)] else 0) +
  (if k = 2 then !![0, coefficientC ρ; 0, coefficientE ρ] else 0)

lemma scaled_entry_stencil (ρ : ℝ) (n : ℕ) (j k : Fin n) (c d : Fin 2) :
    scaledToeplitz ρ n (j, c) (k, d) =
      stencilBlock ρ ((j.val : ℤ) - (k.val : ℤ)) c d := by
  let s : ℤ := (j.val : ℤ) - (k.val : ℤ)
  change (80 : ℂ) *
      (Complex.I * (blockB s c d : ℂ) - (ρ : ℂ) * (blockC s c d : ℂ)) =
    stencilBlock ρ s c d
  by_cases hm : s = -1 <;> by_cases hz : s = 0 <;>
    by_cases hp : s = 1 <;> by_cases ht : s = 2 <;>
    fin_cases c <;> fin_cases d <;>
    simp_all [blockB, blockC, stencilBlock, coefficientA, coefficientB,
      coefficientC, coefficientD, coefficientE, coefficientF,
      Matrix.smul_apply] <;> ring

lemma offset_sum {n : ℕ} (x : BlockVector n) (j s : ℤ) (c : Fin 2) (a : ℂ) :
    (∑ k : Fin n, (if j - (k.val : ℤ) = s then a else 0) * x (k, c)) =
      a * coordinate x (j - s) c := by
  classical
  simp only [coordinate, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have he : j - (k.val : ℤ) = s ↔ (k.val : ℤ) = j - s := by omega
  by_cases h : j - (k.val : ℤ) = s
  · simp [h, he.mp h]
  · simp [h, mt he.mpr h]

lemma stencil_mulVec {n : ℕ} (ρ : ℝ) (x : BlockVector n) (j : Fin n) (c : Fin 2) :
    Matrix.mulVec (scaledToeplitz ρ n) x (j, c) =
      ∑ d : Fin 2,
        (!![coefficientA ρ, 0; coefficientB ρ, 0] c d *
          coordinate x ((j.val : ℤ) + 1) d +
        !![-24 * (ρ : ℂ), coefficientB ρ; 96 * Complex.I, coefficientD ρ] c d *
          coordinate x (j.val : ℤ) d +
        !![coefficientF ρ, 96 * Complex.I; coefficientC ρ, 24 * (ρ : ℂ)] c d *
          coordinate x ((j.val : ℤ) - 1) d +
        !![0, coefficientC ρ; 0, coefficientE ρ] c d *
          coordinate x ((j.val : ℤ) - 2) d) := by
  classical
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp only [scaled_entry_stencil, stencilBlock, Matrix.add_apply, Matrix.ite_apply,
    Matrix.zero_apply, add_mul, Finset.sum_add_distrib]
  simp only [offset_sum, sub_neg_eq_add, sub_zero]

lemma source_row_zero {n : ℕ} (ρ : ℝ) (x : BlockVector n) (j : Fin n) :
    Matrix.mulVec (scaledToeplitz ρ n) x (j, 0) =
      coefficientA ρ * coordinate x ((j.val : ℤ) + 1) 0 -
        24 * (ρ : ℂ) * coordinate x (j.val : ℤ) 0 +
      coefficientF ρ * coordinate x ((j.val : ℤ) - 1) 0 +
      coefficientB ρ * coordinate x (j.val : ℤ) 1 +
      96 * Complex.I * coordinate x ((j.val : ℤ) - 1) 1 +
      coefficientC ρ * coordinate x ((j.val : ℤ) - 2) 1 := by
  rw [stencil_mulVec]
  simp only [Fin.sum_univ_two]
  change coefficientA ρ * coordinate x ((j.val : ℤ) + 1) 0 +
      (-24 * (ρ : ℂ)) * coordinate x (j.val : ℤ) 0 +
      coefficientF ρ * coordinate x ((j.val : ℤ) - 1) 0 +
      0 * coordinate x ((j.val : ℤ) - 2) 0 +
      (0 * coordinate x ((j.val : ℤ) + 1) 1 +
      coefficientB ρ * coordinate x (j.val : ℤ) 1 +
      (96 * Complex.I) * coordinate x ((j.val : ℤ) - 1) 1 +
      coefficientC ρ * coordinate x ((j.val : ℤ) - 2) 1) = _
  ring

lemma source_row_one {n : ℕ} (ρ : ℝ) (x : BlockVector n) (j : Fin n) :
    Matrix.mulVec (scaledToeplitz ρ n) x (j, 1) =
      coefficientB ρ * coordinate x ((j.val : ℤ) + 1) 0 +
      96 * Complex.I * coordinate x (j.val : ℤ) 0 +
      coefficientC ρ * coordinate x ((j.val : ℤ) - 1) 0 +
      coefficientD ρ * coordinate x (j.val : ℤ) 1 +
      24 * (ρ : ℂ) * coordinate x ((j.val : ℤ) - 1) 1 +
      coefficientE ρ * coordinate x ((j.val : ℤ) - 2) 1 := by
  rw [stencil_mulVec]
  simp only [Fin.sum_univ_two]
  change coefficientB ρ * coordinate x ((j.val : ℤ) + 1) 0 +
      (96 * Complex.I) * coordinate x (j.val : ℤ) 0 +
      coefficientC ρ * coordinate x ((j.val : ℤ) - 1) 0 +
      0 * coordinate x ((j.val : ℤ) - 2) 0 +
      (0 * coordinate x ((j.val : ℤ) + 1) 1 +
      coefficientD ρ * coordinate x (j.val : ℤ) 1 +
      (24 * (ρ : ℂ)) * coordinate x ((j.val : ℤ) - 1) 1 +
      coefficientE ρ * coordinate x ((j.val : ℤ) - 2) 1) = _
  ring

#assert_trust kernel source_row_zero
#assert_trust kernel source_row_one

end
end NLA.MF22
