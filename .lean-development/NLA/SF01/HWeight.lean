/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, Cambridge DAMTP.

A positive comparison weight gives genuine unitness by the standard
Gershgorin determinant theorem after column scaling. No diagonal sign is assumed.
-/
import NLA.SF01.SpectralMWeight
import Mathlib.LinearAlgebra.Matrix.Gershgorin

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators Matrix

lemma comparison_mulVec_row {n : ℕ} (A : Square n) (v : Vector n) (i : Fin n) :
    (comparison A *ᵥ v) i =
      |A i i| * v i - ∑ j ∈ Finset.univ.erase i, |A i j| * v j := by
  classical
  have hoff : (∑ j ∈ Finset.univ.erase i, comparison A i j * v j) =
      -(∑ j ∈ Finset.univ.erase i, |A i j| * v j) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp only [comparison, if_neg hji.symm, neg_mul]
  have hdiag : comparison A i i = |A i i| := by simp [comparison]
  calc
    (comparison A *ᵥ v) i =
        (∑ j ∈ Finset.univ.erase i, comparison A i j * v j) + comparison A i i * v i :=
      -- Matrix-vector multiplication is the literal finite row sum.
      (Finset.sum_erase_add Finset.univ (fun j => comparison A i j * v j)
        (Finset.mem_univ i)).symm
    _ = |A i i| * v i - ∑ j ∈ Finset.univ.erase i, |A i j| * v j := by
      rw [hoff, hdiag]
      ring

lemma weighted_comparison_isUnit {n : ℕ} (A : Square n) (v : Vector n)
    (hv : PositiveWeight (comparison A) v) : IsUnit A := by
  classical
  have habs : ∀ j, |v j| = v j := fun j => abs_of_pos (hv.1 j)
  have hscaled : ∀ i, (∑ j ∈ Finset.univ.erase i, ‖(A * Matrix.diagonal v) i j‖) <
      ‖(A * Matrix.diagonal v) i i‖ := by
    intro i
    have hi := hv.2 i
    rw [comparison_mulVec_row] at hi
    have hdd := sub_pos.mp hi
    simpa only [Matrix.mul_diagonal, norm_mul, Real.norm_eq_abs, habs] using hdd
  have hdetprod : (A * Matrix.diagonal v).det ≠ 0 := det_ne_zero_of_sum_row_lt_diag hscaled
  apply (Matrix.isUnit_iff_isUnit_det A).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hdet
  apply hdetprod
  rw [Matrix.det_mul, hdet, zero_mul]

theorem H_positive_weight {n : ℕ} (hn : 1 ≤ n) (A : Square n)
    (hA : IsHMatrix A) :
    IsUnit A ∧ PositiveWeight (comparison A) (weightVector (comparison A)) ∧
      comparison A *ᵥ weightVector (comparison A) = (fun _ => 1) := by
  have hC := spectralM_positive_weight hn (comparison A) hA
  have hw : PositiveWeight (comparison A) (weightVector (comparison A)) := by
    refine ⟨hC.2.2.1, ?_⟩
    intro i
    rw [hC.2.2.2]
    exact zero_lt_one
  exact ⟨weighted_comparison_isUnit A (weightVector (comparison A)) hw, hw, hC.2.2.2⟩

end
end NLA.SF01
