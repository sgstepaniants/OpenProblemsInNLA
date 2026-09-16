/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical argument:
Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge.
-/
import NLA.MF07.Definitions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF07

@[simp] lemma matrixProduct_nil {d : ℕ} : matrixProduct ([] : List (Square d)) = 1 := by
  simp [matrixProduct]

@[simp] lemma matrixProduct_cons {d : ℕ} (A : Square d) (w : List (Square d)) :
    matrixProduct (A :: w) = matrixProduct w * A := by
  simp [matrixProduct, List.reverse_cons, List.prod_append]

lemma matrixProduct_append {d : ℕ} (u v : List (Square d)) :
    matrixProduct (u ++ v) = matrixProduct v * matrixProduct u := by
  simp [matrixProduct, List.reverse_append, List.prod_append]

theorem matrix_product_semantics {d : ℕ} :
    matrixProduct ([] : List (Square d)) = 1 ∧
    ∀ w : List (Square d), ∀ A : Square d,
      matrixProduct (w ++ [A]) = A * matrixProduct w := by
  refine ⟨matrixProduct_nil, ?_⟩
  intro w A
  simp [matrixProduct_append]

lemma spectralNorm_nonneg {d : ℕ} (A : Square d) : 0 ≤ spectralNorm A := norm_nonneg _

lemma spectralNorm_mul_le {d : ℕ} (A B : Square d) :
    spectralNorm (A * B) ≤ spectralNorm A * spectralNorm B := by
  simpa only [spectralNorm, map_mul] using
    norm_mul_le (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A)
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) B)

lemma spectralNorm_add_le {d : ℕ} (A B : Square d) :
    spectralNorm (A + B) ≤ spectralNorm A + spectralNorm B := by
  simpa only [spectralNorm, map_add] using
    norm_add_le (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A)
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) B)

lemma spectralNorm_one {d : ℕ} (hd : 1 ≤ d) : spectralNorm (1 : Square d) = 1 := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  simp [spectralNorm]

lemma spectralNorm_smul {d : ℕ} (c : ℂ) (A : Square d) :
    spectralNorm (c • A) = ‖c‖ * spectralNorm A := by
  simp [spectralNorm, map_smul, norm_smul]

lemma continuous_spectralNorm {d : ℕ} : Continuous (spectralNorm (d := d)) := by
  let f : Square d →ₗ[ℂ] (EuclideanVector d →L[ℂ] EuclideanVector d) :=
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap
  exact f.continuous_of_finiteDimensional.norm

lemma continuous_finiteProduct {d n : ℕ} :
    Continuous (fun A : Fin n → Square d => finiteProduct A) := by
  induction n with
  | zero => simpa [finiteProduct, matrixProduct] using continuous_const
  | succ n ih =>
      have ht : Continuous (fun A : Fin (n+1) → Square d =>
          finiteProduct (fun i : Fin n => A i.succ)) :=
        ih.comp (continuous_pi fun i => continuous_apply i.succ)
      have he : (fun A : Fin (n+1) → Square d => finiteProduct A) =
          (fun A : Fin (n+1) → Square d =>
            finiteProduct (fun i : Fin n => A i.succ) * A 0) := by
        funext A
        simp [finiteProduct, List.ofFn_succ, matrixProduct_cons]
      rw [he]
      exact ht.mul (continuous_apply 0)

lemma WordIn_nil {d : ℕ} (M : Set (Square d)) : WordIn M [] := by
  simp [WordIn]

lemma WordIn_cons_iff {d : ℕ} (M : Set (Square d)) (A : Square d) (w : List (Square d)) :
    WordIn M (A :: w) ↔ A ∈ M ∧ WordIn M w := by
  simp [WordIn]

lemma WordIn_append_iff {d : ℕ} (M : Set (Square d)) (u v : List (Square d)) :
    WordIn M (u ++ v) ↔ WordIn M u ∧ WordIn M v := by
  constructor
  · intro h
    exact ⟨fun A hA => h A (List.mem_append.mpr (Or.inl hA)),
      fun A hA => h A (List.mem_append.mpr (Or.inr hA))⟩
  · rintro ⟨hu, hv⟩ A hA
    rcases List.mem_append.mp hA with hA | hA
    · exact hu A hA
    · exact hv A hA

lemma WordIn_ofFn {d n : ℕ} (M : Set (Square d)) (A : Fin n → Square d)
    (hA : ∀ i, A i ∈ M) : WordIn M (List.ofFn A) := by
  exact List.forall_mem_ofFn_iff.mpr hA

lemma word_spectralNorm_le_pow {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (L : ℝ) (hL : 0 ≤ L) (hbound : ∀ A ∈ M, spectralNorm A ≤ L)
    (w : List (Square d)) (hw : WordIn M w) :
    spectralNorm (matrixProduct w) ≤ L ^ w.length := by
  induction w with
  | nil => simp [spectralNorm_one hd]
  | cons A w ih =>
      obtain ⟨hA, hw⟩ := (WordIn_cons_iff M A w).mp hw
      rw [matrixProduct_cons, List.length_cons, pow_succ]
      exact (spectralNorm_mul_le _ _).trans
        (mul_le_mul (ih hw) (hbound A hA) (spectralNorm_nonneg A) (pow_nonneg hL _))

theorem diagonal_inverse {d : ℕ} (σ : Fin d → ℝ) (hσ : ∀ i, σ i ≠ 0) :
    diagonalWeights σ * inverseDiagonalWeights σ = 1 ∧
      inverseDiagonalWeights σ * diagonalWeights σ = 1 := by
  have hz : ∀ i, (σ i : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.mpr (hσ i)
  constructor <;> ext i j <;> by_cases hij : i = j <;>
    simp [diagonalWeights, inverseDiagonalWeights, Matrix.diagonal_apply,
      Matrix.one_apply, hij, hz]

#print axioms matrix_product_semantics
#assert_trust kernel matrix_product_semantics
#print axioms diagonal_inverse
#assert_trust kernel diagonal_inverse
#print axioms word_spectralNorm_le_pow
#assert_trust kernel word_spectralNorm_le_pow

end NLA.MF07
