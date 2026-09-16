/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The literal complex PSD condition implies normalization of every conditional
pivot law, including uniform dummy labels at the zero residual.
-/
import NLA.RA02.PivotAlgebra
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

@[simp] lemma realTrace_zero (n : ℕ) : realTrace (0 : Square n) = 0 := by
  simp [realTrace]

lemma realTrace_eq_sum {n : ℕ} (A : Square n) :
    realTrace A = ∑ j : Fin n, (A j j).re := by
  simp [realTrace, Matrix.trace, Matrix.diag]

lemma realTrace_nonneg {n : ℕ} {A : Square n} (hA : A.PosSemidef) :
    0 ≤ realTrace A := by
  exact (Complex.nonneg_iff.mp hA.trace_nonneg).1

lemma realTrace_eq_zero_iff {n : ℕ} {A : Square n} (hA : A.PosSemidef) :
    realTrace A = 0 ↔ A = 0 := by
  constructor
  · intro ht
    apply hA.trace_eq_zero_iff.mp
    apply Complex.ext
    · exact ht
    · exact (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm
  · rintro rfl
    exact realTrace_zero n

lemma realTrace_pos {n : ℕ} {A : Square n} (hA : A.PosSemidef) (hne : A ≠ 0) :
    0 < realTrace A := by
  have ht : realTrace A ≠ 0 := fun h => hne ((realTrace_eq_zero_iff hA).mp h)
  exact lt_of_le_of_ne (realTrace_nonneg hA) (Ne.symm ht)

lemma diagonal_real_nonneg {n : ℕ} {A : Square n} (hA : A.PosSemidef) (j : Fin n) :
    0 ≤ (A j j).re := by
  exact (Complex.nonneg_iff.mp (hA.diag_nonneg (i := j))).1

lemma pivotMass_nonneg {n : ℕ} {A : Square n} (hA : A.PosSemidef) (j : Fin n) :
    0 ≤ pivotMass A j := by
  unfold pivotMass
  split_ifs with ht
  · exact div_nonneg zero_le_one (Nat.cast_nonneg n)
  · exact div_nonneg (diagonal_real_nonneg hA j) (realTrace_nonneg hA)

lemma sum_pivotMass (n : ℕ) (hn : 1 ≤ n) (A : Square n) :
    (∑ j : Fin n, pivotMass A j) = 1 := by
  classical
  by_cases ht : realTrace A = 0
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp only [pivotMass, if_pos ht, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp [hn0]
  · simp only [pivotMass, if_neg ht]
    rw [← Finset.sum_div, ← realTrace_eq_sum, div_self ht]

theorem pivot_kernel (n : ℕ) (hn : 1 ≤ n) (A : Square n) (hA : A.PosSemidef) :
    0 ≤ realTrace A ∧ (realTrace A = 0 ↔ A = 0) ∧
    (∀ j : Fin n, 0 ≤ pivotMass A j) ∧ (∑ j : Fin n, pivotMass A j) = 1 ∧
    (A ≠ 0 → 0 < realTrace A ∧
      ∀ j : Fin n, pivotMass A j = (A j j).re / realTrace A ∧
        (A j j = 0 → pivotMass A j = 0)) ∧
    ∀ j : Fin n, (choleskyStep A j).PosSemidef := by
  refine ⟨realTrace_nonneg hA, realTrace_eq_zero_iff hA, pivotMass_nonneg hA,
    sum_pivotMass n hn A, ?_, choleskyStep_posSemidef A hA⟩
  intro hne
  have ht := realTrace_pos hA hne
  refine ⟨ht, ?_⟩
  intro j
  refine ⟨by simp only [pivotMass, if_neg ht.ne'], ?_⟩
  intro hj
  simp [pivotMass, ht.ne', hj]

#print axioms pivot_kernel
#assert_trust kernel pivot_kernel

end
end NLA.RA02
