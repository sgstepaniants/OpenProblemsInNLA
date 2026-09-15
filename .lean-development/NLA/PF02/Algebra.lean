/-
Copyright (c) 2026 George Stepaniants. Apache 2.0.
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. AI-assisted implementation.
Generic real congruence and trace-factorization lemmas; frozen definitions unchanged.
-/
import NLA.PF02.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.PF02

lemma congruenceTransform_one {p q k : ℕ} (F : FactorTuple k p q) :
    congruenceTransform (1 : (Mat k)ˣ) F = F := by
  rcases F with ⟨A, B⟩
  simp [congruenceTransform]

lemma congruenceTransform_mul {p q k : ℕ} (S T : (Mat k)ˣ)
    (F : FactorTuple k p q) :
    congruenceTransform (S * T) F =
      congruenceTransform T (congruenceTransform S F) := by
  apply Prod.ext <;> funext i <;>
    simp [congruenceTransform, Matrix.transpose_mul, Matrix.mul_assoc]

lemma trace_congruence_pair {k : ℕ} (S : (Mat k)ˣ) (A B : Mat k) :
    (((S : Mat k).transpose * A * (S : Mat k)) *
      (((S⁻¹ : (Mat k)ˣ) : Mat k) * B *
        (((S⁻¹ : (Mat k)ˣ) : Mat k).transpose))).trace = (A * B).trace := by
  have ht : (((S⁻¹ : (Mat k)ˣ) : Mat k).transpose) * (S : Mat k).transpose = 1 := by
    rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  have he : ((S : Mat k).transpose * A * (S : Mat k)) *
      (((S⁻¹ : (Mat k)ˣ) : Mat k) * B *
        (((S⁻¹ : (Mat k)ˣ) : Mat k).transpose)) =
      (S : Mat k).transpose * (A * B) *
        (((S⁻¹ : (Mat k)ˣ) : Mat k).transpose) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (S : Mat k) ((S⁻¹ : (Mat k)ˣ) : Mat k),
      Units.mul_inv, Matrix.one_mul]
  rw [he, Matrix.trace_mul_cycle, ht, Matrix.one_mul]

theorem congruence_semantics {p q k : ℕ} (M : Rect p q) :
    (∀ (S : (Mat k)ˣ) (F : FactorizationSpace k M),
      IsPSDFactorization M (congruenceTransform S (F : FactorTuple k p q))) ∧
    Equivalence (CongruenceRel (k := k) (M := M)) := by
  constructor
  · intro S F
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simpa only [congruenceTransform, Matrix.conjTranspose_eq_transpose_of_trivial] using
        (F.property.1 i).conjTranspose_mul_mul_same (S : Mat k)
    · intro j
      simpa only [congruenceTransform, Matrix.conjTranspose_eq_transpose_of_trivial] using
        (F.property.2.1 j).mul_mul_conjTranspose_same
          (((S⁻¹ : (Mat k)ˣ) : Mat k))
    · intro i j
      exact (trace_congruence_pair S (F.val.1 i) (F.val.2 j)).trans
        (F.property.2.2 i j)
  · refine ⟨?_, ?_, ?_⟩
    · intro F
      exact ⟨1, (congruenceTransform_one F.val).symm⟩
    · intro F G h
      rcases h with ⟨S, hS⟩
      refine ⟨S⁻¹, ?_⟩
      rw [hS, ← congruenceTransform_mul]
      simp [congruenceTransform_one]
    · intro F G H hFG hGH
      rcases hFG with ⟨S, hS⟩
      rcases hGH with ⟨T, hT⟩
      exact ⟨S * T, by rw [hT, hS, congruenceTransform_mul]⟩

theorem quotient_topology_semantics {p q k : ℕ} (M : Rect p q) :
    (inferInstance : TopologicalSpace (FactorizationOrbit k M)) =
      TopologicalSpace.coinduced
        (orbitMk : FactorizationSpace k M → FactorizationOrbit k M)
        (inferInstance : TopologicalSpace (FactorizationSpace k M)) := by
  rfl

/-- The crude full-entry factorization already excludes factor sizes one and two.
No symmetric-dimension theorem or minimal-rank default is needed. -/
lemma factorization_rank_le_square {p q k : ℕ} (M : Rect p q)
    (F : FactorizationSpace k M) : M.rank ≤ k * k := by
  let U : Matrix (Fin p) (Fin k × Fin k) ℝ := fun i a => F.val.1 i a.1 a.2
  let V : Matrix (Fin k × Fin k) (Fin q) ℝ := fun a j => F.val.2 j a.2 a.1
  have he : M = U * V := by
    ext i j
    rw [← F.property.2.2 i j]
    change (∑ a : Fin k, ∑ b : Fin k,
      F.val.1 i a b * F.val.2 j b a) =
      ∑ ab : Fin k × Fin k, F.val.1 i ab.1 ab.2 * F.val.2 j ab.2 ab.1
    exact (Fintype.sum_prod_type
      (fun ab : Fin k × Fin k => F.val.1 i ab.1 ab.2 * F.val.2 j ab.2 ab.1)).symm
  rw [he]
  exact (Matrix.rank_mul_le_left U V).trans
    (by simpa using Matrix.rank_le_card_width U)

#assert_trust kernel congruence_semantics
#print axioms congruence_semantics
#assert_trust kernel quotient_topology_semantics
#print axioms quotient_topology_semantics
#assert_trust kernel factorization_rank_le_square
#print axioms factorization_rank_le_square
end NLA.PF02
