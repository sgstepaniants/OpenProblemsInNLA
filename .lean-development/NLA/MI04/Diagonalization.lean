/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

The full complex normal-matrix spectral theorem, obtained from the commuting
Hermitian real and imaginary parts and the complete joint eigenbasis.
-/
import NLA.MI04.JointBasis
import Mathlib.LinearAlgebra.Complex.Module

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04

lemma normal_operator_eigenbasis {n : ℕ}
    (T : CVector (Fin n) →L[ℂ] CVector (Fin n)) (hT : IsStarNormal T) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (CVector (Fin n)), ∃ z : Fin n → ℂ,
      ∀ i, T (b i) = z i • b i := by
  let A : CVector (Fin n) →L[ℂ] CVector (Fin n) := realPart T
  let B : CVector (Fin n) →L[ℂ] CVector (Fin n) := imaginaryPart T
  have hA : (A : Module.End ℂ (CVector (Fin n))).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (selfAdjoint.isSelfAdjoint (x := realPart T))
  have hB : (B : Module.End ℂ (CVector (Fin n))).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
      (selfAdjoint.isSelfAdjoint (x := imaginaryPart T))
  have hAB : Commute A B := by
    letI : IsScalarTower ℂ
        (CVector (Fin n) →L[ℂ] CVector (Fin n))
        (CVector (Fin n) →L[ℂ] CVector (Fin n)) where
      smul_assoc c S U := by
        apply ContinuousLinearMap.ext
        intro v
        change c • S (U v) = c • S (U v)
        rfl
    letI : SMulCommClass ℂ
        (CVector (Fin n) →L[ℂ] CVector (Fin n))
        (CVector (Fin n) →L[ℂ] CVector (Fin n)) where
      smul_comm c S U := by
        apply ContinuousLinearMap.ext
        intro v
        change c • S (U v) = S (c • U v)
        exact (S.map_smul c (U v)).symm
    exact isStarNormal_iff_commute_realPart_imaginaryPart.mp hT
  have hlin : Commute (A : Module.End ℂ (CVector (Fin n)))
      (B : Module.End ℂ (CVector (Fin n))) := by
    exact congrArg (fun S : CVector (Fin n) →L[ℂ] CVector (Fin n) =>
      (S : Module.End ℂ (CVector (Fin n)))) hAB.eq
  obtain ⟨b, α, β, hb⟩ := commuting_symmetric_eigenbasis A B hA hB hlin
  refine ⟨b, fun i => α i + Complex.I * β i, ?_⟩
  intro i
  have ha : A (b i) = α i • b i := (hb i).1
  have hb' : B (b i) = β i • b i := (hb i).2
  calc
    T (b i) = (A + Complex.I • B) (b i) :=
      congrArg (fun S : CVector (Fin n) →L[ℂ] CVector (Fin n) => S (b i))
        (realPart_add_I_smul_imaginaryPart T).symm
    _ = (α i + Complex.I * β i) • b i := by
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ha, hb', smul_smul, add_smul]

theorem normal_unitary_diagonalization {n : ℕ} (hn : 1 ≤ n) (X : Square n)
    (hX : X.conjTranspose * X = X * X.conjTranspose) :
    ∃ U : Matrix.unitaryGroup (Fin n) ℂ, ∃ z : Fin n → ℂ,
      X = (U : Square n) * Matrix.diagonal z * (U : Square n).conjTranspose := by
  let T := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) X
  have hT : IsStarNormal T := by
    letI : IsStarNormal X := ⟨by
      change X.conjTranspose * X = X * X.conjTranspose
      exact hX⟩
    exact IsStarNormal.map
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) X
  obtain ⟨b, z, hb⟩ := normal_operator_eigenbasis T hT
  let U := basisUnitary b
  have hcolumns : X * (U : Square n) = (U : Square n) * Matrix.diagonal z := by
    ext i j
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [U, basisUnitary_entry]
    have h := congrArg (fun v : CVector (Fin n) => v i) (hb j)
    change (∑ k, X i k * b j k) = z j * b j i at h
    simpa only [mul_comm] using h
  have hU : (U : Square n) * (U : Square n).conjTranspose = 1 :=
    Unitary.coe_mul_star_self U
  refine ⟨U, z, ?_⟩
  calc
    X = X * ((U : Square n) * (U : Square n).conjTranspose) := by
      rw [hU, mul_one]
    _ = (X * (U : Square n)) * (U : Square n).conjTranspose := by
      rw [Matrix.mul_assoc]
    _ = (U : Square n) * Matrix.diagonal z * (U : Square n).conjTranspose := by
      rw [hcolumns]

#print axioms normal_unitary_diagonalization
#assert_trust kernel normal_unitary_diagonalization

end NLA.MI04
