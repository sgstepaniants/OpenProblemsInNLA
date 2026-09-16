/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

The four generic trailing-sum identities are copied from accepted IE14/Tail
at 6e48f25fffdae2cf93e4985dc515abbd15e0481b, retaining its IE05 provenance.
The new prefix theorem below handles the actual arbitrary physical row labels;
no cyclic witness, full prescribed suffix or admissibility is imported.
-/
import NLA.IE13.Origin
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators
namespace NLA.IE13

def tailEntry {n : ℕ} (L U : Mat n) (k : ℕ) (i j : Fin n) : ℂ :=
  ∑ a : Fin n, if k ≤ a.val then L i a * U a j else 0

theorem tail_zero {n : ℕ} (L U : Mat n) (i j : Fin n) :
    tailEntry L U 0 i j = (L*U) i j := by
  simp [tailEntry, Matrix.mul_apply]

theorem tail_pivot_row {n : ℕ} (L U : Mat n) (hL : L.IsLowerTriangular)
    (hd : ∀ i, L i i=1) (k j : Fin n) : tailEntry L U k.val k j = U k j := by
  unfold tailEntry
  rw [Finset.sum_eq_single k]
  · simp [hd]
  · intro a _ ha
    by_cases hka : k ≤ a
    · have hlt : k < a := lt_of_le_of_ne hka (Ne.symm ha)
      have hz : L k a=0 := hL hlt
      simp [hka, hz]
    · simp [hka]
  · simp

theorem tail_pivot_column {n : ℕ} (L U : Mat n) (hU : U.IsUpperTriangular)
    (k i : Fin n) : tailEntry L U k.val i k = L i k * U k k := by
  unfold tailEntry
  rw [Finset.sum_eq_single k]
  · simp
  · intro a _ ha
    by_cases hka : k ≤ a
    · have hlt : k < a := lt_of_le_of_ne hka (Ne.symm ha)
      have hz : U a k=0 := hU hlt
      simp [hka, hz]
    · simp [hka]
  · simp

theorem tail_split {n : ℕ} (L U : Mat n) (k i j : Fin n) :
    tailEntry L U k.val i j = L i k * U k j + tailEntry L U (k.val+1) i j := by
  unfold tailEntry
  calc
    (∑ a : Fin n, if k.val ≤ a.val then L i a * U a j else 0) =
        ∑ a : Fin n, ((if a=k then L i k * U k j else 0) +
          (if k.val+1 ≤ a.val then L i a * U a j else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a=k
      · subst a; simp
      · have hne : a.val ≠ k.val := fun h => ha (Fin.ext h)
        by_cases hka : k.val ≤ a.val
        · simp [ha,hka,show k.val+1 ≤ a.val by omega]
        · simp [ha,hka,show ¬k.val+1 ≤ a.val by omega]
    _ = L i k * U k j + ∑ a : Fin n,
        if k.val+1 ≤ a.val then L i a * U a j else 0 := by
      rw [Finset.sum_add_distrib]
      simp

lemma relabeled_LU_prefix_trajectory {n : ℕ} (A L U : Mat n)
    (f : Fin n → Fin n) (path : PivotPath n) (T : ℕ)
    (hA : ∀ i j, A i j = (L * U) (f i) j)
    (hL : L.IsLowerTriangular) (hd : ∀ i, L i i = 1)
    (hU : U.IsUpperTriangular) (hpos : PositionsValid path)
    (hdiag : ∀ k : Fin n, k.val < T → U k k ≠ 0)
    (hlabel : ∀ k : Fin n, k.val < T → f (origin path k.val (path k)) = k)
    (k : ℕ) (hk : k ≤ T) (hkn : k < n) (i j : Fin n)
    (hi : k ≤ i.val) (hj : k ≤ j.val) :
    trajectory A path k i j = tailEntry L U k (f (origin path k i)) j := by
  induction k generalizing i j with
  | zero =>
    simpa only [trajectory, origin, Equiv.refl_apply, tail_zero] using hA i j
  | succ k ih =>
    have hkn' : k < n := by omega
    let z : Fin n := ⟨k, hkn'⟩
    let a : Fin n := path z
    let r : Fin n := Equiv.swap z a i
    have hza : z ≤ a := hpos z
    have hkr : k ≤ r.val := swap_active z a i hza (by omega)
    have hzi : z < i := by exact hi
    have hzj : z < j := by exact hj
    have hpj := ih (by omega) hkn' a j hza (by omega)
    have hpk := ih (by omega) hkn' a z hza le_rfl
    have hrj := ih (by omega) hkn' r j hkr (by omega)
    have hrk := ih (by omega) hkn' r z hkr le_rfl
    have hl : f (origin path k a) = z := hlabel z (by omega)
    rw [hl, tail_pivot_row L U hL hd z j] at hpj
    rw [hl, tail_pivot_row L U hL hd z z] at hpk
    rw [tail_pivot_column L U hU z] at hrk
    rw [trajectory, dif_pos hkn']
    simp only [schurStep, rowSwap, Equiv.swap_apply_left]
    change (if z < i ∧ z < j then trajectory A path k r j -
      (trajectory A path k r z / trajectory A path k a z) * trajectory A path k a j
      else 0) = _
    rw [if_pos ⟨hzi, hzj⟩, hrj, hrk, hpk, hpj,
      mul_div_cancel_right₀ _ (hdiag z (by omega)), tail_split L U z]
    have hnext : f (origin path k r) = f (origin path (k + 1) i) := by
      rw [origin_step path k hkn'] <;> rfl
    rw [hnext]
    ring

lemma relabeled_LU_prefix_admissible {n : ℕ} (A L U : Mat n)
    (f : Fin n → Fin n) (path : PivotPath n) (T : ℕ)
    (hA : ∀ i j, A i j = (L * U) (f i) j)
    (hL : L.IsLowerTriangular) (hd : ∀ i, L i i = 1)
    (hU : U.IsUpperTriangular) (hpos : PositionsValid path)
    (hdiag : ∀ k : Fin n, k.val < T → U k k ≠ 0)
    (hlabel : ∀ k : Fin n, k.val < T → f (origin path k.val (path k)) = k)
    (hnorm : ∀ k : Fin n, k.val < T → ∀ i, ‖L i k‖ ≤ 1) :
    AdmissiblePrefix A path T := by
  intro k hk
  have hp : k ≤ path k := hpos k
  have hcol : ∀ i : Fin n, k ≤ i →
      trajectory A path k.val i k = L (f (origin path k.val i)) k * U k k := by
    intro i hi
    rw [relabeled_LU_prefix_trajectory A L U f path T hA hL hd hU hpos hdiag hlabel
      k.val hk.le k.isLt i k hi le_rfl, tail_pivot_column L U hU k]
  have hpiv : trajectory A path k.val (path k) k = U k k := by
    rw [hcol _ hp, hlabel k hk, hd k, one_mul]
  refine ⟨hp, ?_, ?_⟩
  · rw [hpiv]
    exact hdiag k hk
  · intro i hi
    rw [hcol i hi, hpiv, norm_mul]
    exact (mul_le_mul_of_nonneg_right (hnorm k hk _) (norm_nonneg _)).trans_eq (one_mul _)

lemma relabeled_LU_nonsingular {n : ℕ} (A L U : Mat n) (f : Equiv.Perm (Fin n))
    (hA : ∀ i j, A i j = (L * U) (f i) j)
    (hL : L.IsLowerTriangular) (hd : ∀ i, L i i = 1)
    (hU : U.IsUpperTriangular) (hdiag : ∀ i, U i i ≠ 0) : A.det ≠ 0 := by
  have hmat : A = (L * U).submatrix f id := by ext i j; exact hA i j
  rw [hmat, Matrix.det_permute, Matrix.det_mul,
    Matrix.det_of_isLowerTriangular _ hL, Matrix.det_of_isUpperTriangular hU]
  apply mul_ne_zero
  · exact_mod_cast (Units.ne_zero (Equiv.Perm.sign f))
  · apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro i _
      rw [hd]
      exact one_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => hdiag i)

#print axioms relabeled_LU_prefix_trajectory
#assert_trust kernel relabeled_LU_prefix_trajectory
#print axioms relabeled_LU_prefix_admissible
#assert_trust kernel relabeled_LU_prefix_admissible
#print axioms relabeled_LU_nonsingular
#assert_trust kernel relabeled_LU_nonsingular

end NLA.IE13
