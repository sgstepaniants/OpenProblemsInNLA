/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The genuine rank-at-most-one consequence of simple characteristic roots.
This proves the required boundary sandwich even when its scalar is zero;
the independent numerator/denominator argument proves that scalar nonzero.
-/
import NLA.MF22.ProjectorAlgebra
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF22

open Polynomial
open scoped BigOperators

lemma nodal_rootMultiplicity_one {n : ℕ} (nodes : Fin n → ℂ)
    (hnodes : Function.Injective nodes) (i : Fin n) :
    (Lagrange.nodal Finset.univ nodes).rootMultiplicity (nodes i) = 1 := by
  have hmul : (X - C (nodes i)) *
      Lagrange.nodal (Finset.univ.erase i) nodes ≠ 0 :=
    mul_ne_zero (Polynomial.monic_X_sub_C (nodes i)).ne_zero Lagrange.nodal_ne_zero
  have hno : ¬(Lagrange.nodal (Finset.univ.erase i) nodes).IsRoot (nodes i) := by
    apply Lagrange.eval_nodal_not_at_node
    intro j hj
    exact hnodes.ne (Ne.symm (Finset.mem_erase.mp hj).1)
  rw [Lagrange.nodal_eq_mul_nodal_erase (Finset.mem_univ i),
    Polynomial.rootMultiplicity_mul hmul, Polynomial.rootMultiplicity_X_sub_C_self,
    Polynomial.rootMultiplicity_eq_zero hno, add_zero]

lemma transfer_eigenspace_finrank_le_one_of_charpoly (ρ : ℝ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots)
    (hchar : (transferMatrix ρ).charpoly = C ((leadingScalar ρ)⁻¹) * quartic ρ)
    (i : Fin 4) :
    Module.finrank ℂ (Module.End.eigenspace (transferMatrix ρ).toLin' (roots i)) ≤ 1 := by
  have he := LinearMap.finrank_eigenspace_le (transferMatrix ρ).toLin' (roots i)
  rw [Matrix.charpoly_toLin', transfer_charpoly_eq_nodal ρ roots hroots hchar,
    nodal_rootMultiplicity_one roots hroots.1 i] at he
  exact he

/-- Every column lying in a space of dimension at most one makes all
two-by-two minors zero. No nonzero column or nonzero coordinate is assumed. -/
lemma entry_minor_zero_of_simple_eigenspace {n : ℕ} (A P : Square n) (z : ℂ)
    (hAP : A * P = z • P)
    (hdim : Module.finrank ℂ (Module.End.eigenspace A.toLin' z) ≤ 1)
    (r k c s : Fin n) :
    P r c * P k s = P k c * P r s := by
  let E := Module.End.eigenspace A.toLin' z
  have hcol (j : Fin n) : (fun row => P row j) ∈ E := by
    apply Module.End.mem_eigenspace_iff.mpr
    change Matrix.mulVec A (fun row => P row j) = z • (fun row => P row j)
    funext row
    exact congrArg (fun M : Square n => M row j) hAP
  obtain ⟨w, hw⟩ := (finrank_le_one_iff (K := ℂ) (V := E)).mp hdim
  choose coeff hcoeff using fun j : Fin n => hw ⟨(fun row => P row j), hcol j⟩
  have hentry (row j : Fin n) : P row j = coeff j * (w : Fin n → ℂ) row := by
    have he := congrArg (fun v : E => (v : Fin n → ℂ) row) (hcoeff j)
    simpa only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul] using he.symm
  simp only [hentry]
  ring

lemma spectralProjector_entry_minor_zero_of_charpoly (ρ : ℝ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots)
    (hchar : (transferMatrix ρ).charpoly = C ((leadingScalar ρ)⁻¹) * quartic ρ)
    (i r k c s : Fin 4) :
    spectralProjector ρ roots i r c * spectralProjector ρ roots i k s =
      spectralProjector ρ roots i k c * spectralProjector ρ roots i r s := by
  exact entry_minor_zero_of_simple_eigenspace (transferMatrix ρ)
    (spectralProjector ρ roots i) (roots i)
    (transfer_mul_spectralProjector_of_charpoly ρ roots hroots hchar i)
    (transfer_eigenspace_finrank_le_one_of_charpoly ρ roots hroots hchar i) r k c s

/-- The actual boundary rank-one matrix has only its (0,0) entry nonzero. -/
lemma boundaryOuter_eq_single_outer :
    boundaryOuter = Matrix.vecMulVec (Pi.single 0 (1 : ℂ)) (Pi.single 0 (1 : ℂ)) := by
  have hb : boundaryVector = Pi.single 0 (1 : ℂ) := by
    funext i
    fin_cases i <;> rfl
  change Matrix.vecMulVec boundaryVector boundaryVector = _
  rw [hb]

/-- The full matrix sandwich required for cancellation of growing Green
terms. It is derived from simple-root eigenspace dimension, not idempotence. -/
lemma spectralProjector_boundary_sandwich_of_charpoly (ρ : ℝ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots)
    (hchar : (transferMatrix ρ).charpoly = C ((leadingScalar ρ)⁻¹) * quartic ρ)
    (i : Fin 4) :
    spectralProjector ρ roots i * boundaryOuter * spectralProjector ρ roots i =
      spectralProjector ρ roots i 0 0 • spectralProjector ρ roots i := by
  rw [boundaryOuter_eq_single_outer, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.mulVec_single_one, Matrix.single_one_vecMul]
  ext r s
  exact spectralProjector_entry_minor_zero_of_charpoly ρ roots hroots hchar i r 0 0 s

#assert_trust kernel transfer_eigenspace_finrank_le_one_of_charpoly
#print axioms transfer_eigenspace_finrank_le_one_of_charpoly
#assert_trust kernel spectralProjector_entry_minor_zero_of_charpoly
#print axioms spectralProjector_entry_minor_zero_of_charpoly
#assert_trust kernel spectralProjector_boundary_sandwich_of_charpoly
#print axioms spectralProjector_boundary_sandwich_of_charpoly

end NLA.MF22
