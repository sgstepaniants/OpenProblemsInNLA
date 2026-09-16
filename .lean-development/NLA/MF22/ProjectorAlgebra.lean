/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

All algebraic identities for the frozen, actual Lagrange projectors.
The only matrix-specific input is the separately proved characteristic formula.
-/
import NLA.MF22.ProjectorPolynomial

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF22

open Polynomial
open scoped BigOperators

lemma aeval_eq_sum_smul_projector (ρ : ℝ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots)
    (hchar : (transferMatrix ρ).charpoly = C ((leadingScalar ρ)⁻¹) * quartic ρ)
    (p : ℂ[X]) :
    aeval (transferMatrix ρ) p =
      ∑ i : Fin 4, p.eval (roots i) • spectralProjector ρ roots i := by
  have he := matrix_aeval_eq_of_eval_nodes (transferMatrix ρ) roots hroots.1
    (transfer_charpoly_eq_nodal ρ roots hroots hchar) p
    (Lagrange.interpolate Finset.univ roots (fun i => p.eval (roots i)))
    (fun i => (Lagrange.eval_interpolate_at_node (fun k => p.eval (roots k))
      hroots.1.injOn (Finset.mem_univ i)).symm)
  simpa only [Lagrange.interpolate_apply, map_sum, map_mul, aeval_C,
    ← Algebra.smul_def, spectralProjector] using he

lemma spectralProjector_mul_of_charpoly (ρ : ℝ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots)
    (hchar : (transferMatrix ρ).charpoly = C ((leadingScalar ρ)⁻¹) * quartic ρ)
    (i j : Fin 4) :
    spectralProjector ρ roots i * spectralProjector ρ roots j =
      if i = j then spectralProjector ρ roots i else 0 := by
  by_cases hij : i = j
  · subst j
    have he := matrix_aeval_eq_of_eval_nodes (transferMatrix ρ) roots hroots.1
      (transfer_charpoly_eq_nodal ρ roots hroots hchar)
      (Lagrange.basis Finset.univ roots i * Lagrange.basis Finset.univ roots i)
      (Lagrange.basis Finset.univ roots i) (by
        intro k
        rw [eval_mul, lagrange_basis_eval_node roots hroots.1 i k]
        split_ifs <;> simp)
    simpa only [spectralProjector, map_mul, if_pos rfl] using he
  · have he := matrix_aeval_eq_of_eval_nodes (transferMatrix ρ) roots hroots.1
      (transfer_charpoly_eq_nodal ρ roots hroots hchar)
      (Lagrange.basis Finset.univ roots i * Lagrange.basis Finset.univ roots j)
      0 (by
        intro k
        rw [eval_mul, eval_zero]
        by_cases hik : i = k
        · subst k
          rw [Lagrange.eval_basis_of_ne (Ne.symm hij) (Finset.mem_univ i), mul_zero]
        · rw [Lagrange.eval_basis_of_ne hik (Finset.mem_univ k), zero_mul])
    simpa only [spectralProjector, map_mul, map_zero, if_neg hij] using he

/-- The range of each actual projector lies in the corresponding eigenspace. -/
lemma transfer_mul_spectralProjector_of_charpoly (ρ : ℝ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots)
    (hchar : (transferMatrix ρ).charpoly = C ((leadingScalar ρ)⁻¹) * quartic ρ)
    (i : Fin 4) :
    transferMatrix ρ * spectralProjector ρ roots i =
      roots i • spectralProjector ρ roots i := by
  have he := matrix_aeval_eq_of_eval_nodes (transferMatrix ρ) roots hroots.1
    (transfer_charpoly_eq_nodal ρ roots hroots hchar)
    (X * Lagrange.basis Finset.univ roots i)
    (C (roots i) * Lagrange.basis Finset.univ roots i) (by
      intro k
      simp only [eval_mul, eval_X, eval_C]
      by_cases hik : i = k
      · subst k
        rfl
      · rw [Lagrange.eval_basis_of_ne hik (Finset.mem_univ k)]
        simp only [mul_zero])
  simpa only [spectralProjector, map_mul, aeval_X, aeval_C,
    ← Algebra.smul_def] using he

lemma spectralProjector_mul_transfer_of_charpoly (ρ : ℝ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots)
    (hchar : (transferMatrix ρ).charpoly = C ((leadingScalar ρ)⁻¹) * quartic ρ)
    (i : Fin 4) :
    spectralProjector ρ roots i * transferMatrix ρ =
      roots i • spectralProjector ρ roots i := by
  calc
    spectralProjector ρ roots i * transferMatrix ρ =
        transferMatrix ρ * spectralProjector ρ roots i := by
      have he := congrArg (aeval (transferMatrix ρ))
        (mul_comm (Lagrange.basis Finset.univ roots i) X)
      simpa only [spectralProjector, map_mul, aeval_X] using he
    _ = roots i • spectralProjector ρ roots i :=
      transfer_mul_spectralProjector_of_charpoly ρ roots hroots hchar i

/-- Exact frozen algebraic conjunction, conditional only on the separately
proved formula for the actual transfer matrix's characteristic polynomial. -/
theorem spectral_projector_algebra_of_charpoly (ρ : ℝ) (hρ : 0 < ρ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots)
    (hchar : (transferMatrix ρ).charpoly = C ((leadingScalar ρ)⁻¹) * quartic ρ) :
    (∑ i : Fin 4, spectralProjector ρ roots i) = 1 ∧
    (∀ i j : Fin 4,
      spectralProjector ρ roots i * spectralProjector ρ roots j =
        if i = j then spectralProjector ρ roots i else 0) ∧
    ∀ j : ℕ, transferMatrix ρ ^ j =
      ∑ i : Fin 4, (roots i ^ j) • spectralProjector ρ roots i := by
  refine ⟨?_, spectralProjector_mul_of_charpoly ρ roots hroots hchar, ?_⟩
  · have he := aeval_eq_sum_smul_projector ρ roots hroots hchar 1
    simpa only [map_one, eval_one, one_smul] using he.symm
  · intro j
    simpa only [aeval_X_pow, eval_pow, eval_X] using
      (aeval_eq_sum_smul_projector ρ roots hroots hchar (X ^ j))

#assert_trust kernel aeval_eq_sum_smul_projector
#print axioms aeval_eq_sum_smul_projector
#assert_trust kernel transfer_mul_spectralProjector_of_charpoly
#print axioms transfer_mul_spectralProjector_of_charpoly
#assert_trust kernel spectral_projector_algebra_of_charpoly
#print axioms spectral_projector_algebra_of_charpoly

end NLA.MF22
