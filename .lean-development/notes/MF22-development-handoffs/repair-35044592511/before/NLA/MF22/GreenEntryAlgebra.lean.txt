/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The exact Green decomposition uses the rank-one boundary identity before
estimating entries. Every matrix product estimated here has inner dimension
four, independent of the original Toeplitz dimension.
-/
import NLA.MF22.GreenKernel
import NLA.MF22.Norms

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open scoped BigOperators

noncomputable section

def greenLeadingCoefficient (ρ : ℝ) (roots : Fin 4 → ℂ) (n j ell : ℕ) : ℂ :=
  (if ell < j then roots 3 ^ (j - 1 - ell) else 0) -
    (boundaryScalar ρ n)⁻¹ * dominantGamma ρ roots * roots 3 ^ j *
      roots 3 ^ (n - 1 - ell)

lemma transfer_power_decomposition (ρ : ℝ) (roots : Fin 4 → ℂ) (j : ℕ) :
    transferMatrix ρ ^ j =
      (roots 3 ^ j) • spectralProjector ρ roots 3 + spectralRemainder ρ roots j := by
  unfold spectralRemainder
  abel

lemma green_expansion_of_sandwich (ρ : ℝ) (roots : Fin 4 → ℂ)
    (hsandwich : spectralProjector ρ roots 3 * boundaryOuter * spectralProjector ρ roots 3 =
      dominantGamma ρ roots • spectralProjector ρ roots 3) (n j ell : ℕ) :
    greenKernel ρ n j ell =
      greenLeadingCoefficient ρ roots n j ell •
        (spectralProjector ρ roots 3 * forcingMatrix ρ) +
      (if ell < j then spectralRemainder ρ roots (j - 1 - ell) * forcingMatrix ρ else 0) -
      ((boundaryScalar ρ n)⁻¹ * roots 3 ^ j) •
        (spectralProjector ρ roots 3 * boundaryOuter *
          spectralRemainder ρ roots (n - 1 - ell) * forcingMatrix ρ) -
      ((boundaryScalar ρ n)⁻¹ * roots 3 ^ (n - 1 - ell)) •
        (spectralRemainder ρ roots j * boundaryOuter *
          spectralProjector ρ roots 3 * forcingMatrix ρ) -
      (boundaryScalar ρ n)⁻¹ •
        (spectralRemainder ρ roots j * boundaryOuter *
          spectralRemainder ρ roots (n - 1 - ell) * forcingMatrix ρ) := by
  by_cases h : ell < j
  all_goals
    simp only [greenKernel, greenLeadingCoefficient, h, if_true, if_false,
      transfer_power_decomposition, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, hsandwich, smul_add, smul_sub, smul_smul]
    module

lemma norm_four_product_entry_bound {ι κ : Type*}
    (A : Matrix ι (Fin 4) ℂ) (B : Matrix (Fin 4) κ ℂ)
    (a b : ℝ) (ha : 0 ≤ a) (hA : ∀ r t, ‖A r t‖ ≤ a)
    (hB : ∀ t s, ‖B t s‖ ≤ b) (r : ι) (s : κ) :
    ‖(A * B) r s‖ ≤ 4 * a * b := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ t : Fin 4, ‖A r t * B t s‖ := norm_sum_le _ _
    _ ≤ ∑ _t : Fin 4, a * b := by
      apply Finset.sum_le_sum
      intro t _
      rw [norm_mul]
      exact mul_le_mul (hA r t) (hB t s) (norm_nonneg _) ha
    _ = 4 * a * b := by simp [Fin.sum_univ_four] <;> ring

lemma norm_boundary_four_product_bound {ι : Type*}
    (A B : Square 4) (G : Matrix (Fin 4) ι ℂ)
    (a b g : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : ∀ r t, ‖A r t‖ ≤ a) (hB : ∀ r t, ‖B r t‖ ≤ b)
    (hG : ∀ r s, ‖G r s‖ ≤ g) (r : Fin 4) (s : ι) :
    ‖(A * boundaryOuter * B * G) r s‖ ≤ a * (4 * b * g) := by
  rw [boundary_four_product, norm_mul]
  exact mul_le_mul (hA r 0)
    (norm_four_product_entry_bound B G b g hb hB hG 0 s)
    (norm_nonneg _) ha

lemma norm_five_terms_bound (x y u v w : ℂ) :
    ‖x + y - u - v - w‖ ≤ ‖x‖ + ‖y‖ + ‖u‖ + ‖v‖ + ‖w‖ := by
  have h₁ := norm_add_le x y
  have h₂ := norm_sub_le (x + y) u
  have h₃ := norm_sub_le (x + y - u) v
  have h₄ := norm_sub_le (x + y - u - v) w
  linarith

def forcingEntryBound (ρ : ℝ) : ℝ :=
  (∑ r : Fin 4, ∑ s : Fin 2, ‖forcingMatrix ρ r s‖) + 1

lemma forcingEntryBound_pos (ρ : ℝ) : 0 < forcingEntryBound ρ := by
  unfold forcingEntryBound
  positivity

lemma forcing_entry_bound (ρ : ℝ) (r : Fin 4) (s : Fin 2) :
    ‖forcingMatrix ρ r s‖ ≤ forcingEntryBound ρ := by
  have h₁ : ‖forcingMatrix ρ r s‖ ≤ ∑ t : Fin 2, ‖forcingMatrix ρ r t‖ :=
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  have h₂ : (∑ t : Fin 2, ‖forcingMatrix ρ r t‖) ≤
      ∑ k : Fin 4, ∑ t : Fin 2, ‖forcingMatrix ρ k t‖ :=
    Finset.single_le_sum
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ r)
  unfold forcingEntryBound
  linarith

#assert_trust kernel green_expansion_of_sandwich
#assert_trust kernel norm_boundary_four_product_bound

end
end NLA.MF22
