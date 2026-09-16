/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The frozen false state is the actual distinguished-pivot residual. Its PSD
and all active diagonal positivity follow without a Schur-complement axiom.
-/
import NLA.RA02.ArrowheadQuadratic
import NLA.RA02.PivotAlgebra

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

lemma state_true_last_pivot (r : ℕ) (U : Finset (Fin r)) :
    choleskyStep (arrowheadState r U true) (Fin.last r) = arrowheadState r U false := by
  have hpivot : arrowheadState r U true (Fin.last r) (Fin.last r) ≠ 0 := by
    rw [state_true_last_last]
    exact_mod_cast (cornerValue_pos r U).ne'
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simpa only [state_false_last_row] using
      choleskyStep_pivot_row (arrowheadState r U true) (Fin.last r) hpivot j
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [state_false_last_col] using
        choleskyStep_pivot_col (arrowheadState r U true) (Fin.last r) hpivot i.castSucc
    · simp only [choleskyStep, hpivot, ↓reduceIte, state_true_ordinary,
        state_true_ordinary_last, state_true_last_ordinary, state_true_last_last,
        state_false_ordinary]
      by_cases hi : i ∈ U <;> by_cases hj : j ∈ U <;> by_cases hij : i = j <;>
        simp_all [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div]

lemma state_false_posSemidef (r : ℕ) (U : Finset (Fin r)) :
    (arrowheadState r U false).PosSemidef := by
  rw [← state_true_last_pivot]
  exact choleskyStep_posSemidef (arrowheadState r U true)
    (state_true_posSemidef r U) (Fin.last r)

theorem residual_state_positivity (r : ℕ) (hr : 1 ≤ r) (U : Finset (Fin r)) :
    0 < cornerValue r U ∧
    (∀ b : Bool, (arrowheadState r U b).PosSemidef) ∧
    ∀ i ∈ U,
      ((arrowheadState r U true) i.castSucc i.castSucc).re = diagonalWeight r i.val ∧
      ((arrowheadState r U false) i.castSucc i.castSucc).re =
        diagonalWeight r i.val * cornerValue r (U.erase i) / cornerValue r U ∧
      0 < ((arrowheadState r U true) i.castSucc i.castSucc).re ∧
      0 < ((arrowheadState r U false) i.castSucc i.castSucc).re := by
  refine ⟨cornerValue_pos r U, ?_, ?_⟩
  · intro b
    cases b
    · exact state_false_posSemidef r U
    · exact state_true_posSemidef r U
  · intro i hi
    refine ⟨state_true_diagonal r U i hi, state_false_diagonal r U i hi, ?_, ?_⟩
    · rw [state_true_diagonal r U i hi]
      exact diagonalWeight_pos r i.val
    · rw [state_false_diagonal r U i hi]
      exact div_pos (mul_pos (diagonalWeight_pos r i.val)
        (cornerValue_pos r (U.erase i))) (cornerValue_pos r U)

#print axioms state_true_last_pivot
#assert_trust kernel state_true_last_pivot
#print axioms state_false_posSemidef
#assert_trust kernel state_false_posSemidef
#print axioms residual_state_positivity
#assert_trust kernel residual_state_positivity

end
end NLA.RA02
