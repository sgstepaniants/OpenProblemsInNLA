/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Restrict the complete joint-eigenspace decomposition to the finite sets of
actual eigenvalues. Multiplicities remain inside the subspaces; no simple
spectrum or invertibility is required.
-/
import NLA.MI04.BasisTransport
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04

private lemma exists_subordinate_basis {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (V : ι → Submodule ℂ (CVector (Fin n)))
    (horth : OrthogonalFamily ℂ (fun i => V i) (fun i => (V i).subtypeₗᵢ))
    (htop : (⨆ i, V i) = ⊤) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (CVector (Fin n)),
      ∃ j : Fin n → ι, ∀ i, b i ∈ V (j i) := by
  have hdim : Module.finrank ℂ (CVector (Fin n)) = n := finrank_euclideanSpace_fin
  have hV : DirectSum.IsInternal V := horth.isInternal_iff.mpr (by
    rw [htop, Submodule.top_orthogonal_eq_bot])
  refine ⟨hV.subordinateOrthonormalBasis hdim horth,
    fun i => hV.subordinateOrthonormalBasisIndex hdim i horth, ?_⟩
  intro i
  exact hV.subordinateOrthonormalBasis_subordinate hdim i horth

private def jointEigenSpace {n : ℕ}
    (A B : Module.End ℂ (CVector (Fin n)))
    (j : Module.End.Eigenvalues B × Module.End.Eigenvalues A) :
    Submodule ℂ (CVector (Fin n)) :=
  Module.End.eigenspace A j.2.val ⊓ Module.End.eigenspace B j.1.val

private lemma jointEigenSpace_orthogonal {n : ℕ}
    (A B : Module.End ℂ (CVector (Fin n)))
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    OrthogonalFamily ℂ (fun j => jointEigenSpace A B j)
      (fun j => (jointEigenSpace A B j).subtypeₗᵢ) := by
  have hinj : Function.Injective
      (fun j : Module.End.Eigenvalues B × Module.End.Eigenvalues A =>
        (j.1.val, j.2.val)) := by
    intro j k h
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst h)
    · exact Subtype.ext (congrArg Prod.snd h)
  apply OrthogonalFamily.of_pairwise (V := jointEigenSpace A B)
  intro j k hjk
  exact (hA.orthogonalFamily_eigenspace_inf_eigenspace hB).pairwise
    (hinj.ne hjk)

private lemma jointEigenSpace_iSup {n : ℕ}
    (A B : Module.End ℂ (CVector (Fin n)))
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    (⨆ j, jointEigenSpace A B j) = ⊤ := by
  apply le_antisymm le_top
  rw [← hA.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hB hAB]
  refine iSup_le fun α => iSup_le fun β => ?_
  by_cases hα : Module.End.HasEigenvalue A α
  · by_cases hβ : Module.End.HasEigenvalue B β
    · exact le_iSup (jointEigenSpace A B) (⟨β, hβ⟩, ⟨α, hα⟩)
    · have hzero : Module.End.eigenspace B β = ⊥ := by
        by_contra hne
        exact hβ (Module.End.hasEigenvalue_iff.mpr hne)
      rw [hzero, inf_bot_eq]
      exact bot_le
  · have hzero : Module.End.eigenspace A α = ⊥ := by
      by_contra hne
      exact hα (Module.End.hasEigenvalue_iff.mpr hne)
    rw [hzero, bot_inf_eq]
    exact bot_le

set_option maxHeartbeats 800000 in
lemma commuting_symmetric_eigenbasis {n : ℕ}
    (A B : Module.End ℂ (CVector (Fin n)))
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
    ∃ b : OrthonormalBasis (Fin n) ℂ (CVector (Fin n)),
      ∃ α β : Fin n → ℂ, ∀ i, A (b i) = α i • b i ∧ B (b i) = β i • b i := by
  classical
  obtain ⟨b, j, hj⟩ := exists_subordinate_basis (jointEigenSpace A B)
    (jointEigenSpace_orthogonal A B hA hB) (jointEigenSpace_iSup A B hA hB hAB)
  refine ⟨b, fun i => (j i).2.val, fun i => (j i).1.val, ?_⟩
  intro i
  have hm : b i ∈ jointEigenSpace A B (j i) := hj i
  change b i ∈ Module.End.eigenspace A (j i).2.val ⊓
    Module.End.eigenspace B (j i).1.val at hm
  exact ⟨Module.End.mem_eigenspace_iff.mp hm.1,
    Module.End.mem_eigenspace_iff.mp hm.2⟩

#print axioms commuting_symmetric_eigenbasis
#assert_trust kernel commuting_symmetric_eigenbasis

end NLA.MI04
