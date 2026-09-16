import Mathlib

/- Statements-only draft for the complete IV-03 interval criterion.
Mathematical source: Matthew J. Colbrook, IV-03.tex, Theorem 1.
AI-assisted formalization draft prepared for Sidney Holden. -/
set_option autoImplicit false
noncomputable section
namespace NLA.IV03

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- An actual nonsingular, entrywise nonnegative matrix whose inverse has
nonpositive off-diagonal entries. No regularity of a whole interval is assumed. -/
def IsInverseM {n : ℕ} (A : Mat n) : Prop :=
  IsUnit A ∧ (∀ i j, 0 ≤ A i j) ∧ ∀ i j, i ≠ j → A⁻¹ i j ≤ 0

def OrderedEndpoints {n : ℕ} (L U : Mat n) : Prop := ∀ i j, L i j ≤ U i j

def intervalFamily {n : ℕ} (L U : Mat n) : Set (Mat n) :=
  {A | ∀ i j, L i j ≤ A i j ∧ A i j ≤ U i j}

def center {n : ℕ} (L U : Mat n) : Mat n := fun i j => (L i j + U i j) / 2
def radius {n : ℕ} (L U : Mat n) : Mat n := fun i j => (U i j - L i j) / 2

def signVector {n : ℕ} (i : Fin n) (k : Fin n) : ℝ := if k = i then -1 else 1

/-- Entrywise expression for C+s D_i R D_j, with the exact original D_i. -/
def vertex {n : ℕ} (L U : Mat n) (s : ℝ) (i j : Fin n) : Mat n :=
  fun k l => center L U k l + s * signVector i k * radius L U k l * signVector j l

def TwoSignCriterion : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ L U : Mat n, OrderedEndpoints L U →
    ((∀ A ∈ intervalFamily L U, IsInverseM A) ↔
      ∀ i j : Fin n, ∀ s ∈ ({(-1 : ℝ), 1} : Set ℝ), IsInverseM (vertex L U s i j))

end NLA.IV03
