/- Determinant of the actual symmetric congruence action, by sparse generators.
Mathematics: Matthew J. Colbrook. Formalization: George Stepaniants, Caltech CMS.
Apache 2.0; AI-assisted. No large determinant or interval calculation is expanded. -/
import NLA.PF02.CongruenceReduction
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.PF02

private lemma congruence_diagonal_det (d : Fin 3 → ℝ) :
    (congruenceCoordinateMatrix (Matrix.diagonal d)).det =
      (Matrix.diagonal d).det ^ 4 := by
  have hd : congruenceCoordinateMatrix (Matrix.diagonal d) =
      Matrix.diagonal (![d 0 ^ 2, d 1 ^ 2, d 2 ^ 2,
        d 0 * d 1, d 0 * d 2, d 1 * d 2] : Fin 6 → ℝ) := by
    rw [congruence_coordinate_entries]
    ext i j
    fin_cases i <;> fin_cases j
    · change ((d 0) ^ 2 : ℝ) = d 0 ^ 2
      ring
    · change ((0) ^ 2 : ℝ) = 0
      ring
    · change ((0) ^ 2 : ℝ) = 0
      ring
    · change ((d 0) * (0) : ℝ) = 0
      ring
    · change ((d 0) * (0) : ℝ) = 0
      ring
    · change ((0) * (0) : ℝ) = 0
      ring
    · change ((0) ^ 2 : ℝ) = 0
      ring
    · change ((d 1) ^ 2 : ℝ) = d 1 ^ 2
      ring
    · change ((0) ^ 2 : ℝ) = 0
      ring
    · change ((0) * (d 1) : ℝ) = 0
      ring
    · change ((0) * (0) : ℝ) = 0
      ring
    · change ((d 1) * (0) : ℝ) = 0
      ring
    · change ((0) ^ 2 : ℝ) = 0
      ring
    · change ((0) ^ 2 : ℝ) = 0
      ring
    · change ((d 2) ^ 2 : ℝ) = d 2 ^ 2
      ring
    · change ((0) * (0) : ℝ) = 0
      ring
    · change ((0) * (d 2) : ℝ) = 0
      ring
    · change ((0) * (d 2) : ℝ) = 0
      ring
    · change (2 * (d 0) * (0) : ℝ) = 0
      ring
    · change (2 * (0) * (d 1) : ℝ) = 0
      ring
    · change (2 * (0) * (0) : ℝ) = 0
      ring
    · change ((d 0) * (d 1) + (0) * (0) : ℝ) = d 0 * d 1
      ring
    · change ((d 0) * (0) + (0) * (0) : ℝ) = 0
      ring
    · change ((0) * (0) + (0) * (d 1) : ℝ) = 0
      ring
    · change (2 * (d 0) * (0) : ℝ) = 0
      ring
    · change (2 * (0) * (0) : ℝ) = 0
      ring
    · change (2 * (0) * (d 2) : ℝ) = 0
      ring
    · change ((d 0) * (0) + (0) * (0) : ℝ) = 0
      ring
    · change ((d 0) * (d 2) + (0) * (0) : ℝ) = d 0 * d 2
      ring
    · change ((0) * (d 2) + (0) * (0) : ℝ) = 0
      ring
    · change (2 * (0) * (0) : ℝ) = 0
      ring
    · change (2 * (d 1) * (0) : ℝ) = 0
      ring
    · change (2 * (0) * (d 2) : ℝ) = 0
      ring
    · change ((0) * (0) + (d 1) * (0) : ℝ) = 0
      ring
    · change ((0) * (d 2) + (0) * (0) : ℝ) = 0
      ring
    · change ((d 1) * (d 2) + (0) * (0) : ℝ) = d 1 * d 2
      ring
  rw [hd, Matrix.det_diagonal, Matrix.det_diagonal]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change (d 0 ^ 2 * (d 1 ^ 2 * (d 2 ^ 2 *
    (d 0 * d 1 * (d 0 * d 2 * (d 1 * d 2)))))) = (d 0 * (d 1 * d 2)) ^ 4
  ring

/-- Reordering both coordinate axes preserves the determinant. -/
private lemma det_one_of_reordered_triangular (A : Mat 6) (e : Equiv.Perm (Fin 6))
    (ht : (A.submatrix e e).IsUpperTriangular) (hd : ∀ i, A i i = 1) :
    A.det = 1 := by
  rw [← Matrix.det_submatrix_equiv_self e A, Matrix.det_of_isUpperTriangular ht]
  simp [Matrix.submatrix_apply, hd]

/-- A topological order of the sparse coordinate arrows for E_{01}. -/
private def order01 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (![0, 3, 1, 4, 5, 2] : Fin 6 → Fin 6) (by decide)

private lemma congruence_transvection_01_det (c : ℝ) :
    (congruenceCoordinateMatrix (Matrix.transvection (0 : Fin 3) 1 c)).det = 1 := by
  rw [congruence_coordinate_entries]
  apply det_one_of_reordered_triangular _ order01
  · intro a b hab
    change b.val < a.val at hab
    fin_cases a <;> fin_cases b
    · exact False.elim ((by decide : ¬ ((0 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((1 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 0)) hab)
    · change (2 * ((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((1 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 1)) hab)
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 2)) hab)
    · change (2 * ((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) + ((0 + c)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (2 * ((0 + c)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 3)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 3)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 3)) hab)
    · change (2 * ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((0 + 0)) + ((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (2 * ((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 4)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 4)) hab)
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 5)) hab)
  · intro a
    fin_cases a
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + c)) * ((0 + 0)) : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 1
      ring

/-- A topological order of the sparse coordinate arrows for E_{10}. -/
private def order10 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (![2, 5, 4, 1, 3, 0] : Fin 6 → Fin 6) (by decide)

private lemma congruence_transvection_10_det (c : ℝ) :
    (congruenceCoordinateMatrix (Matrix.transvection (1 : Fin 3) 0 c)).det = 1 := by
  rw [congruence_coordinate_entries]
  apply det_one_of_reordered_triangular _ order10
  · intro a b hab
    change b.val < a.val at hab
    fin_cases a <;> fin_cases b
    · exact False.elim ((by decide : ¬ ((0 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((1 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 0)) hab)
    · change (2 * ((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((1 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 1)) hab)
    · change (2 * ((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 2)) hab)
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + c)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 3)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 3)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 3)) hab)
    · change (2 * ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((0 + 0)) + ((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) + ((0 + 0)) * ((0 + c)) : ℝ) = 0
      ring
    · change (2 * ((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 4)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 4)) hab)
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 5)) hab)
  · intro a
    fin_cases a
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + c)) : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 1
      ring

/-- A topological order of the sparse coordinate arrows for E_{02}. -/
private def order02 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (![0, 4, 2, 3, 5, 1] : Fin 6 → Fin 6) (by decide)

private lemma congruence_transvection_02_det (c : ℝ) :
    (congruenceCoordinateMatrix (Matrix.transvection (0 : Fin 3) 2 c)).det = 1 := by
  rw [congruence_coordinate_entries]
  apply det_one_of_reordered_triangular _ order02
  · intro a b hab
    change b.val < a.val at hab
    fin_cases a <;> fin_cases b
    · exact False.elim ((by decide : ¬ ((0 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((1 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 0)) hab)
    · change (2 * ((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((1 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 1)) hab)
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 2)) hab)
    · change (2 * ((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) + ((0 + c)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (2 * ((0 + c)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 3)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 3)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 3)) hab)
    · change (2 * ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (2 * ((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((0 + 0)) + ((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 4)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 4)) hab)
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 5)) hab)
  · intro a
    fin_cases a
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + c)) * ((0 + 0)) : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 1
      ring

/-- A topological order of the sparse coordinate arrows for E_{20}. -/
private def order20 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (![1, 5, 3, 2, 4, 0] : Fin 6 → Fin 6) (by decide)

private lemma congruence_transvection_20_det (c : ℝ) :
    (congruenceCoordinateMatrix (Matrix.transvection (2 : Fin 3) 0 c)).det = 1 := by
  rw [congruence_coordinate_entries]
  apply det_one_of_reordered_triangular _ order20
  · intro a b hab
    change b.val < a.val at hab
    fin_cases a <;> fin_cases b
    · exact False.elim ((by decide : ¬ ((0 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((1 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 0)) hab)
    · change (2 * ((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((1 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 1)) hab)
    · change (2 * ((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((0 + 0)) + ((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 2)) hab)
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · change (((0 + c)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 3)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 3)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 3)) hab)
    · change (2 * ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) + ((0 + 0)) * ((0 + c)) : ℝ) = 0
      ring
    · change (2 * ((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 4)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 4)) hab)
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 5)) hab)
  · intro a
    fin_cases a
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + c)) : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 1
      ring

/-- A topological order of the sparse coordinate arrows for E_{12}. -/
private def order12 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (![1, 5, 2, 3, 4, 0] : Fin 6 → Fin 6) (by decide)

private lemma congruence_transvection_12_det (c : ℝ) :
    (congruenceCoordinateMatrix (Matrix.transvection (1 : Fin 3) 2 c)).det = 1 := by
  rw [congruence_coordinate_entries]
  apply det_one_of_reordered_triangular _ order12
  · intro a b hab
    change b.val < a.val at hab
    fin_cases a <;> fin_cases b
    · exact False.elim ((by decide : ¬ ((0 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((1 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 0)) hab)
    · change (2 * ((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((1 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 1)) hab)
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 2)) hab)
    · change (2 * ((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((0 + c)) + ((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · change (2 * ((0 + 0)) * ((0 + c)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 3)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 3)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 3)) hab)
    · change (2 * ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (2 * ((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 4)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 4)) hab)
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 5)) hab)
  · intro a
    fin_cases a
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + c)) * ((0 + 0)) : ℝ) = 1
      ring

/-- A topological order of the sparse coordinate arrows for E_{21}. -/
private def order21 : Equiv.Perm (Fin 6) :=
  Equiv.ofBijective (![0, 4, 3, 2, 5, 1] : Fin 6 → Fin 6) (by decide)

private lemma congruence_transvection_21_det (c : ℝ) :
    (congruenceCoordinateMatrix (Matrix.transvection (2 : Fin 3) 1 c)).det = 1 := by
  rw [congruence_coordinate_entries]
  apply det_one_of_reordered_triangular _ order21
  · intro a b hab
    change b.val < a.val at hab
    fin_cases a <;> fin_cases b
    · exact False.elim ((by decide : ¬ ((0 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((1 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 0)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 0)) hab)
    · change (2 * ((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((1 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 1)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 1)) hab)
    · change (2 * ((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((2 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 2)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 2)) hab)
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((0 + c)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((3 : ℕ) < 3)) hab)
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 3)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 3)) hab)
    · change (2 * ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((0 + c)) + ((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (2 * ((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((4 : ℕ) < 4)) hab)
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 4)) hab)
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((0 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) * ((1 + 0)) : ℝ) = 0
      ring
    · change (((0 + 0)) ^ 2 : ℝ) = 0
      ring
    · change (((1 + 0)) * ((0 + 0)) : ℝ) = 0
      ring
    · exact False.elim ((by decide : ¬ ((5 : ℕ) < 5)) hab)
  · intro a
    fin_cases a
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) ^ 2 : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + 0)) : ℝ) = 1
      ring
    · change (((1 + 0)) * ((1 + 0)) + ((0 + 0)) * ((0 + c)) : ℝ) = 1
      ring

private lemma congruence_transvection_det (t : Matrix.TransvectionStruct (Fin 3) ℝ) :
    (congruenceCoordinateMatrix t.toMatrix).det = 1 := by
  rcases t with ⟨i, j, hij, c⟩
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | exact congruence_transvection_01_det c
    | exact congruence_transvection_02_det c
    | exact congruence_transvection_10_det c
    | exact congruence_transvection_12_det c
    | exact congruence_transvection_20_det c
    | exact congruence_transvection_21_det c

/-- Diagonal and elementary transvection matrices generate every real matrix,
including singular matrices. Sparse triangular checks replace a general 6×6
Laplace expansion. Multiplicativity then gives the full frozen theorem. -/
theorem congruence_coordinate_determinant (S : Mat 3) :
    (congruenceCoordinateMatrix S).det = S.det ^ 4 := by
  apply Matrix.diagonal_transvection_induction
    (fun A : Mat 3 => (congruenceCoordinateMatrix A).det = A.det ^ 4) S
  · intro d _
    exact congruence_diagonal_det d
  · intro t
    simpa only [t.det, one_pow] using congruence_transvection_det t
  · intro A B hA hB
    rw [congruence_coordinate_mul, Matrix.det_mul, Matrix.det_mul, hA, hB, mul_pow]

#assert_trust kernel congruence_coordinate_determinant
#print axioms congruence_coordinate_determinant
end NLA.PF02
