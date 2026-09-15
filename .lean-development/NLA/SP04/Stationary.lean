/-
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. Apache 2.0; AI-assisted.
The reduction covers every real stationary matrix and both determinant signs.
-/
import NLA.SP04.ScalarRoots
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.Fin.Basic

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option leancert.trust "kernel"
open scoped BigOperators
noncomputable section
namespace NLA.SP04

lemma unit_absolute_determinant_ne_zero {n : ℕ} (X : Mat n)
    (hX : UnitAbsoluteDeterminant X) : X.det ≠ 0 := by
  intro hzero
  unfold UnitAbsoluteDeterminant at hX
  rw [hzero, abs_zero] at hX
  norm_num at hX

lemma stationary_transpose_input {n : ℕ} (U X : Mat n) (c : ℝ)
    (hX : StationaryPair U X c) :
    X.transpose * U = X.transpose * X + c • (1 : Mat n) := by
  have h := hX.2
  rw [Matrix.mul_sub] at h
  simpa only [add_comm] using sub_eq_iff_eq_add.mp h

lemma stationary_gram_commutes {n : ℕ} (U X : Mat n) (c : ℝ)
    (hX : StationaryPair U X c) :
    (X.transpose * X) * (U.transpose * U) =
      (U.transpose * U) * (X.transpose * X) := by
  have hdet : X.transpose.det ≠ 0 := by
    simpa only [Matrix.det_transpose] using unit_absolute_determinant_ne_zero X hX.1
  letI : Invertible X.transpose := Matrix.invertibleOfIsUnitDet X.transpose
    (isUnit_iff_ne_zero.mpr hdet)
  have hP := stationary_transpose_input U X c hX
  have hPT : U.transpose * X = X.transpose * X + c • (1 : Mat n) := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add,
      Matrix.transpose_smul, Matrix.transpose_one] using congrArg Matrix.transpose hP
  have hfirst : X.transpose * U = U.transpose * X := hP.trans hPT.symm
  have hleft : U * X.transpose = X * X.transpose + c • (1 : Mat n) := by
    apply Matrix.mul_right_injective_of_invertible X.transpose
    calc
      X.transpose * (U * X.transpose) = (X.transpose * U) * X.transpose :=
        (Matrix.mul_assoc _ _ _).symm
      _ = (X.transpose * X + c • (1 : Mat n)) * X.transpose := by rw [hP]
      _ = X.transpose * (X * X.transpose + c • (1 : Mat n)) := by
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc,
          Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have hright : X * U.transpose = X * X.transpose + c • (1 : Mat n) := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_add,
      Matrix.transpose_smul, Matrix.transpose_one] using congrArg Matrix.transpose hleft
  have hcross : X * U.transpose = U * X.transpose := hright.trans hleft.symm
  calc
    (X.transpose * X) * (U.transpose * U) =
        X.transpose * (X * U.transpose) * U := by simp only [Matrix.mul_assoc]
    _ = X.transpose * (U * X.transpose) * U := by rw [hcross]
    _ = (X.transpose * U) * (X.transpose * U) := by simp only [Matrix.mul_assoc]
    _ = (U.transpose * X) * (U.transpose * X) := by rw [hfirst]
    _ = U.transpose * (X * U.transpose) * X := by simp only [Matrix.mul_assoc]
    _ = U.transpose * (U * X.transpose) * X := by rw [hcross]
    _ = (U.transpose * U) * (X.transpose * X) := by simp only [Matrix.mul_assoc]

lemma orderedBox_strictMono (s : Fin 3 → ℝ) (hs : OrderedBox s) : StrictMono s := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  fin_cases i
  · exact hs.2.1
  · exact hs.2.2.1

lemma orderedBox_sq_ne (s : Fin 3 → ℝ) (hs : OrderedBox s)
    (i j : Fin 3) (hij : i ≠ j) : s i ^ 2 ≠ s j ^ 2 := by
  intro heq
  apply hij
  apply (orderedBox_strictMono s hs).injective
  exact (sq_eq_sq₀ (orderedBox_pos s hs i).le (orderedBox_pos s hs j).le).mp heq

theorem stationary_diagonal_reduction (s : Fin 3 → ℝ) (hs : OrderedBox s)
    (X : Mat 3) (c : ℝ) (hX : StationaryPair (Matrix.diagonal s) X c) :
    ∃ x : Fin 3 → ℝ, X = Matrix.diagonal x ∧
      (∀ i, x i ^ 2 - s i * x i + c = 0) ∧ |∏ i, x i| = 1 := by
  have hgram := stationary_gram_commutes (Matrix.diagonal s) X c hX
  have hG : (Matrix.diagonal s).transpose * Matrix.diagonal s =
      Matrix.diagonal (fun i => s i ^ 2) := by
    simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, pow_two]
  rw [hG] at hgram
  have hSoff : ∀ i j : Fin 3, i ≠ j → (X.transpose * X) i j = 0 := by
    intro i j hij
    have hentry := congrArg (fun M : Mat 3 => M i j) hgram
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at hentry
    have hmul : (X.transpose * X) i j * (s j ^ 2 - s i ^ 2) = 0 := by
      nlinarith [hentry]
    rcases mul_eq_zero.mp hmul with hz | hz
    · exact hz
    · exact (orderedBox_sq_ne s hs j i (Ne.symm hij) (sub_eq_zero.mp hz)).elim
  have hP := stationary_transpose_input (Matrix.diagonal s) X c hX
  have hXoff : ∀ i j : Fin 3, i ≠ j → X i j = 0 := by
    intro i j hij
    have hentry := congrArg (fun M : Mat 3 => M j i) hP
    have hji : j ≠ i := Ne.symm hij
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, if_neg hji,
      hSoff j i hji, mul_zero, zero_add] at hentry
    exact (mul_eq_zero.mp hentry).resolve_right (ne_of_gt (orderedBox_pos s hs i))
  let x : Fin 3 → ℝ := fun i => X i i
  have hdiag : X = Matrix.diagonal x := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, x]
    · simp only [Matrix.diagonal_apply_ne _ hij, hXoff i j hij]
  refine ⟨x, hdiag, ?_, ?_⟩
  · intro i
    have hentry := congrArg (fun M : Mat 3 => M i i) hP
    rw [hdiag] at hentry
    simp only [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_apply_eq, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply_eq, mul_one] at hentry
    nlinarith
  · have hdet := hX.1
    unfold UnitAbsoluteDeterminant at hdet
    rw [hdiag, Matrix.det_diagonal] at hdet
    exact hdet

lemma diagonal_stationary_of_roots {n : ℕ} (s x : Fin n → ℝ) (c : ℝ)
    (hprod : |∏ i, x i| = 1) (hroots : ∀ i, x i ^ 2 - s i * x i + c = 0) :
    StationaryPair (Matrix.diagonal s) (Matrix.diagonal x) c := by
  constructor
  · simpa only [UnitAbsoluteDeterminant, Matrix.det_diagonal] using hprod
  · rw [Matrix.mul_sub, Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply,
        smul_eq_mul, Matrix.one_apply_eq, mul_one]
      nlinarith [hroots i]
    · simp [Matrix.sub_apply, Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply,
        Matrix.one_apply, hij]

#assert_trust kernel stationary_diagonal_reduction
#print axioms stationary_diagonal_reduction
end NLA.SP04
