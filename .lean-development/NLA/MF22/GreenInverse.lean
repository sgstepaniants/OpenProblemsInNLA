/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The finite Green formula reconstructs every source state and gives an actual
two-sided inverse. The original factor eighty is restored explicitly.
-/
import NLA.MF22.GreenKernel
import NLA.MF22.StateReconstruction
import NLA.MF22.SourceRecurrence

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open scoped BigOperators

noncomputable section

def forcedGreenState (ρ : ℝ) (n : ℕ) (f : BlockVector n) (j : ℕ) : Fin 4 → ℂ :=
  ∑ ell : Fin n, Matrix.mulVec (greenKernel ρ n j ell.val)
    (fun c : Fin 2 => f (ell, c))

lemma inverseCandidate_stateCoordinates (ρ : ℝ) (n : ℕ) (f : BlockVector n) :
    Matrix.mulVec (inverseCandidate ρ n) f =
      stateCoordinates n (forcedGreenState ρ n f) := by
  funext row
  obtain ⟨j, c⟩ := row
  by_cases hc : c = 0 <;>
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, inverseCandidate,
      stateCoordinates, forcedGreenState, Finset.sum_apply, hc]

lemma forcedGreenState_initial (ρ : ℝ) (n : ℕ) (f : BlockVector n)
    (r : Fin 4) (hr : r ≠ 0) : forcedGreenState ρ n f 0 r = 0 := by
  simp only [forcedGreenState, Finset.sum_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro ell _
  apply Finset.sum_eq_zero
  intro c _
  rw [greenKernel_initial_zero ρ n ell.val r hr, zero_mul]

lemma forcedGreenState_terminal (ρ : ℝ) (n : ℕ) (f : BlockVector n)
    (ha : boundaryScalar ρ n ≠ 0) : forcedGreenState ρ n f n 0 = 0 := by
  simp only [forcedGreenState, Finset.sum_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro ell _
  apply Finset.sum_eq_zero
  intro c _
  rw [greenKernel_terminal_zero ρ n ell.val ell.isLt ha, zero_mul]

lemma forcedGreenState_shift_two (ρ : ℝ) (n : ℕ) (f : BlockVector n) (j : ℕ) :
    forcedGreenState ρ n f (j + 1) 2 = forcedGreenState ρ n f j 0 := by
  simp only [forcedGreenState, Finset.sum_apply, Matrix.mulVec, dotProduct,
    greenKernel_shift_two]

lemma forcedGreenState_shift_three (ρ : ℝ) (n : ℕ) (f : BlockVector n) (j : ℕ) :
    forcedGreenState ρ n f (j + 1) 3 = forcedGreenState ρ n f j 1 := by
  simp only [forcedGreenState, Finset.sum_apply, Matrix.mulVec, dotProduct,
    greenKernel_shift_three]

theorem green_source_state (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : 1 ≤ n)
    (ha : boundaryScalar ρ n ≠ 0) (f : BlockVector n) (j : ℕ) (hj : j ≤ n) :
    sourceState (Matrix.mulVec (inverseCandidate ρ n) f) j =
      ∑ ell : Fin n, Matrix.mulVec (greenKernel ρ n j ell.val)
        (fun c : Fin 2 => f (ell, c)) := by
  rw [inverseCandidate_stateCoordinates]
  exact reconstruct_state n hn (forcedGreenState ρ n f)
    (forcedGreenState_initial ρ n f) (forcedGreenState_terminal ρ n f ha)
    (fun k _ => forcedGreenState_shift_two ρ n f k)
    (fun k _ => forcedGreenState_shift_three ρ n f k) j hj

lemma mulVec_finset_sum {ι : Type*} (s : Finset ι) (T : Square 4)
    (v : ι → Fin 4 → ℂ) :
    Matrix.mulVec T (∑ i ∈ s, v i) = ∑ i ∈ s, Matrix.mulVec T (v i) := by
  classical
  ext r
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

lemma forcedGreenState_step (ρ : ℝ) (n : ℕ) (f : BlockVector n) (j : Fin n) :
    forcedGreenState ρ n f (j.val + 1) =
      Matrix.mulVec (transferMatrix ρ) (forcedGreenState ρ n f j.val) +
        Matrix.mulVec (forcingMatrix ρ) (fun c : Fin 2 => f (j, c)) := by
  classical
  have hdelta :
      (∑ ell : Fin n, Matrix.mulVec
        (if ell.val = j.val then forcingMatrix ρ else 0)
        (fun c : Fin 2 => f (ell, c))) =
      Matrix.mulVec (forcingMatrix ρ) (fun c : Fin 2 => f (j, c)) := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro ell _ hne
      have hv : ell.val ≠ j.val := by intro he; exact hne (Fin.ext he)
      simp [hv]
    · simp
  unfold forcedGreenState
  simp only [greenKernel_step, Matrix.add_mulVec, ← Matrix.mulVec_mulVec,
    Finset.sum_add_distrib]
  rw [hdelta, ← mulVec_finset_sum]

theorem green_inverse (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : 1 ≤ n)
    (ha : boundaryScalar ρ n ≠ 0) :
    scaledToeplitz ρ n * inverseCandidate ρ n = 1 ∧
    inverseCandidate ρ n * scaledToeplitz ρ n = 1 ∧
    inverseCandidate ρ n = (scaledToeplitz ρ n)⁻¹ ∧
    (toeplitz ρ n).det ≠ 0 ∧
    (toeplitz ρ n)⁻¹ = (80 : ℂ) • inverseCandidate ρ n := by
  have hright : scaledToeplitz ρ n * inverseCandidate ρ n = 1 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro f
    rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
    apply (source_recurrence ρ hρ n hn _ f).mpr
    intro j
    have hj : j.val ≤ n := j.isLt.le
    have hjs : j.val + 1 ≤ n := by omega
    rw [green_source_state ρ hρ n hn ha f (j.val + 1) hjs,
      green_source_state ρ hρ n hn ha f j.val hj]
    exact forcedGreenState_step ρ n f j
  have hleft : inverseCandidate ρ n * scaledToeplitz ρ n = 1 :=
    mul_eq_one_comm.mp hright
  have hH : toeplitz ρ n * ((80 : ℂ) • inverseCandidate ρ n) = 1 := by
    rw [Matrix.mul_smul, ← Matrix.smul_mul]
    exact hright
  exact ⟨hright, hleft, (Matrix.inv_eq_right_inv hright).symm,
    Matrix.det_ne_zero_of_right_inverse hH, Matrix.inv_eq_right_inv hH⟩

#assert_trust kernel green_source_state
#print axioms green_source_state
#assert_trust kernel green_inverse
#print axioms green_inverse

end
end NLA.MF22
