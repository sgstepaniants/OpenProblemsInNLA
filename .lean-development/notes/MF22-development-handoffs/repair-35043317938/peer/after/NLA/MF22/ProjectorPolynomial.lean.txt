/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Polynomial equality modulo the actual matrix characteristic polynomial.
Distinct nodes provide divisibility; Cayley--Hamilton performs the evaluation.
No diagonalization or projector property is assumed.
-/
import NLA.MF22.Definitions
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import LeanCert.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF22

open Polynomial
open scoped BigOperators

lemma nodal_dvd_of_eval_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (hnodes : Function.Injective nodes) (p : ℂ[X])
    (hp : ∀ i, p.eval (nodes i) = 0) :
    Lagrange.nodal Finset.univ nodes ∣ p := by
  simpa only [Lagrange.nodal] using
    (Fintype.prod_dvd_of_coprime (Polynomial.pairwise_coprime_X_sub_C hnodes)
      (fun i => Polynomial.dvd_iff_isRoot.mpr (hp i)))

/-- Four simple roots identify the monic characteristic polynomial; its
degree comes from the actual four-dimensional matrix, not the source formula. -/
lemma transfer_charpoly_eq_nodal (ρ : ℝ) (roots : Fin 4 → ℂ)
    (hroots : RootData ρ roots)
    (hchar : (transferMatrix ρ).charpoly = C ((leadingScalar ρ)⁻¹) * quartic ρ) :
    (transferMatrix ρ).charpoly = Lagrange.nodal Finset.univ roots := by
  apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (Lagrange.nodal_monic (s := Finset.univ) (v := roots))
    (Matrix.charpoly_monic (transferMatrix ρ))
  · apply nodal_dvd_of_eval_eq_zero roots hroots.1
    intro i
    have hi : (quartic ρ).eval (roots i) = 0 := (hroots.2.1 i).2
    rw [hchar]
    simp only [eval_mul, eval_C, hi, mul_zero]
  · simp only [Matrix.charpoly_natDegree_eq_dim, Lagrange.natDegree_nodal,
      Finset.card_univ, le_refl]

/-- Equality on all distinct characteristic roots suffices for equality
after evaluation at the matrix. The polynomial degrees are unrestricted. -/
lemma matrix_aeval_eq_of_eval_nodes {n : ℕ} (A : Square n)
    (nodes : Fin n → ℂ) (hnodes : Function.Injective nodes)
    (hchar : A.charpoly = Lagrange.nodal Finset.univ nodes)
    (p q : ℂ[X]) (hpq : ∀ i, p.eval (nodes i) = q.eval (nodes i)) :
    aeval A p = aeval A q := by
  have hdiv : A.charpoly ∣ p - q := by
    rw [hchar]
    apply nodal_dvd_of_eval_eq_zero nodes hnodes
    intro i
    rw [eval_sub, hpq i, sub_self]
  have he := Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero hdiv
    (Matrix.aeval_self_charpoly A)
  simpa only [map_sub, sub_eq_zero] using he

lemma lagrange_basis_eval_node {n : ℕ} (nodes : Fin n → ℂ)
    (hnodes : Function.Injective nodes) (i j : Fin n) :
    (Lagrange.basis Finset.univ nodes i).eval (nodes j) =
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simpa using
      (Lagrange.eval_basis_self hnodes.injOn (Finset.mem_univ i))
  · simpa only [if_neg hij] using
      (Lagrange.eval_basis_of_ne hij (Finset.mem_univ j))

#assert_trust kernel transfer_charpoly_eq_nodal
#print axioms transfer_charpoly_eq_nodal
#assert_trust kernel matrix_aeval_eq_of_eval_nodes
#print axioms matrix_aeval_eq_of_eval_nodes

end NLA.MF22
