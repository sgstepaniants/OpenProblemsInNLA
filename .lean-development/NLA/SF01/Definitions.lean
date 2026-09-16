/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology. AI-assisted statement draft.
Original mathematics: Matthew J. Colbrook, Cambridge DAMTP.
Planned maximum-principle reuse: Sidney Holden's Apache-2.0 IV-03 formalization.

Definitions only. The original spectral H predicate is retained. No matrix
unitness, positive-weight equivalence, spectral decomposition or Newton
preservation theorem is assumed by a definition or a structure field.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped BigOperators

abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev Vector (n : ℕ) := Fin n → ℝ

def complexify {n : ℕ} (A : Square n) : Matrix (Fin n) (Fin n) ℂ :=
  A.map Complex.ofReal

/-- The complex algebraic spectrum, including nonreal eigenvalues of real A. -/
def complexSpectrum {n : ℕ} (A : Square n) : Set ℂ := spectrum ℂ (complexify A)

/-- The actual finite-spectrum maximum is an independent Challenge obligation. -/
def spectralRadius {n : ℕ} (A : Square n) : ℝ :=
  sSup ((fun z : ℂ => ‖z‖) '' complexSpectrum A)

def EntrywiseNonnegative {n : ℕ} (A : Square n) : Prop := ∀ i j, 0 ≤ A i j

def IsZMatrix {n : ℕ} (A : Square n) : Prop := ∀ i j, i ≠ j → A i j ≤ 0

def PositiveDiagonal {n : ℕ} (A : Square n) : Prop := ∀ i, 0 < A i i

def comparison {n : ℕ} (A : Square n) : Square n :=
  fun i j => if i = j then |A i j| else -|A i j|

/-- The original nonsingular M-matrix definition, not a weighted surrogate. -/
def IsSpectralM {n : ℕ} (C : Square n) : Prop :=
  ∃ s : ℝ, ∃ B : Square n,
    EntrywiseNonnegative B ∧ C = s • (1 : Square n) - B ∧ spectralRadius B < s

def IsHMatrix {n : ℕ} (A : Square n) : Prop := IsSpectralM (comparison A)

def Admissible {n : ℕ} (A : Square n) : Prop := IsHMatrix A ∧ PositiveDiagonal A

def PositiveWeight {n : ℕ} (C : Square n) (v : Vector n) : Prop :=
  (∀ i, 0 < v i) ∧ ∀ i, 0 < (C *ᵥ v) i

def weightVector {n : ℕ} (C : Square n) : Vector n := C⁻¹ *ᵥ (fun _ => 1)

def shifted {n : ℕ} (A : Square n) (t : ℝ) : Square n := A + t • (1 : Square n)

def spectralHomotopy {n : ℕ} (s : ℝ) (B : Square n) (t : ℝ) : Square n :=
  s • (1 : Square n) - t • B

/-- The exact original recurrence. Its matrices are proved to be units; the
totalized matrix inverse on arbitrary inputs is not a substitute for that proof. -/
def newton {n : ℕ} (A : Square n) : ℕ → Square n
  | 0 => A
  | k + 1 => (1 / 2 : ℝ) • (newton A k + (newton A k)⁻¹ * A)

/-- Finite scalar data only. In particular there is no theorem-valued field. -/
structure RidgeData where
  size : ℕ
  a : ℝ
  b : ℝ
  poles : Fin size → ℝ
  weights : Fin size → ℝ

def ValidData (d : RidgeData) : Prop :=
  0 < d.a ∧ 0 < d.b ∧ (∀ j, 0 < d.poles j) ∧ ∀ j, 0 ≤ d.weights j

def ridgeEval {n : ℕ} (d : RidgeData) (A : Square n) : Square n :=
  d.a • (1 : Square n) + d.b • A +
    ∑ j : Fin d.size, d.weights j • (A * (shifted A (d.poles j))⁻¹)

/-- Exact empty-family representation of the first iterate. -/
def initialData : RidgeData where
  size := 0
  a := 1 / 2
  b := 1 / 2
  poles := Fin.elim0
  weights := Fin.elim0

def poleOffsets (d : RidgeData) : Fin (d.size + 1) → ℝ := Fin.cases 0 d.poles

def poleVector (d : RidgeData) : Fin (d.size + 1) → ℝ :=
  Fin.cases (Real.sqrt d.a) (fun j => Real.sqrt (d.weights j))

def poleMatrix (d : RidgeData) : Square (d.size + 1) :=
  Matrix.diagonal (poleOffsets d) +
    d.b⁻¹ • (fun i j => poleVector d i * poleVector d j)

def IsOrthogonal {n : ℕ} (Q : Square n) : Prop :=
  Q.transpose * Q = 1 ∧ Q * Q.transpose = 1

/-- An actual finite matrix identity, whose existence must be proved. -/
def PoleDiagonalization (d : RidgeData) (Q : Square (d.size + 1))
    (lam : Fin (d.size + 1) → ℝ) : Prop :=
  IsOrthogonal Q ∧ (∀ i, 0 < lam i) ∧
    poleMatrix d = Q * Matrix.diagonal lam * Q.transpose

def spectralCoordinates (d : RidgeData) (Q : Square (d.size + 1)) :
    Fin (d.size + 1) → ℝ := Q.transpose *ᵥ poleVector d

def reciprocalWeights (d : RidgeData) (Q : Square (d.size + 1))
    (lam : Fin (d.size + 1) → ℝ) : Fin (d.size + 1) → ℝ :=
  fun i => spectralCoordinates d Q i ^ 2 / (d.b ^ 2 * lam i)

def reciprocalEval {n : ℕ} (d : RidgeData) (Q : Square (d.size + 1))
    (lam : Fin (d.size + 1) → ℝ) (A : Square n) : Square n :=
  ∑ i : Fin (d.size + 1), reciprocalWeights d Q lam i • (A * (shifted A (lam i))⁻¹)

abbrev BlockSquare (d : RidgeData) (n : ℕ) :=
  Matrix (Fin (d.size + 1) × Fin n) (Fin (d.size + 1) × Fin n) ℝ

def baseBlock {n : ℕ} (d : RidgeData) (A : Square n) : BlockSquare d n :=
  Matrix.kronecker (1 : Square (d.size + 1)) A +
    Matrix.kronecker (Matrix.diagonal (poleOffsets d)) (1 : Square n)

def poleBlock {n : ℕ} (d : RidgeData) (A : Square n) : BlockSquare d n :=
  Matrix.kronecker (1 : Square (d.size + 1)) A +
    Matrix.kronecker (poleMatrix d) (1 : Square n)

end
end NLA.SF01
