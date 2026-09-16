/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted statement draft.

Original retained mathematical proof: George Stepaniants. The original
Toeplitz family, question and source root classification are due to Bogoya,
Böttcher, Ferrari, Grudsky and Serra-Capizzano. Definitions only: no proof
implementation, statement approval or machine acceptance is claimed.
-/
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.ENNReal.Real
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

set_option autoImplicit false

namespace NLA.MF22

open Polynomial
open scoped BigOperators Classical ENNReal

noncomputable section

abbrev Square (d : ℕ) := Matrix (Fin d) (Fin d) ℂ
abbrev BlockIndex (n : ℕ) := Fin n × Fin 2
abbrev BlockMatrix (n : ℕ) := Matrix (BlockIndex n) (BlockIndex n) ℂ
abbrev BlockVector (n : ℕ) := BlockIndex n → ℂ

/-- The genuine induced complex Euclidean operator norm for the displayed
finite index type; no default entrywise matrix norm is substituted. -/
def spectralNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A‖

/-- Singular matrices have infinite condition number, including when the
totalized nonsingular inverse happens to be zero. -/
def conditionNumber {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) : ℝ≥0∞ :=
  if A.det = 0 then ⊤ else ENNReal.ofReal (spectralNorm A * spectralNorm A⁻¹)

/-- Literal coefficient blocks from the original permanent MF-22 statement. -/
def blockB (k : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if k = -1 then (3 / 40 : ℝ) • !![-1, 0; -5, 0]
  else if k = 0 then (3 / 40 : ℝ) • !![0, -5; 16, -5]
  else if k = 1 then (3 / 40 : ℝ) • !![-5, 16; -5, 0]
  else if k = 2 then (3 / 40 : ℝ) • !![0, -5; 0, -1]
  else 0

def blockC (k : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  if k = -1 then (1 / 80 : ℝ) • !![1, 0; 7, 0]
  else if k = 0 then (1 / 80 : ℝ) • !![24, 7; 0, 25]
  else if k = 1 then (1 / 80 : ℝ) • !![-25, 0; -7, -24]
  else if k = 2 then (1 / 80 : ℝ) • !![0, -7; 0, -1]
  else 0

/-- The original pure Toeplitz truncation, with no corner corrections.
The first coordinate is the block index, and offsets use integer subtraction. -/
def toeplitz (ρ : ℝ) (n : ℕ) : BlockMatrix n := fun row col =>
  Complex.I * (blockB ((row.1.val : ℤ) - (col.1.val : ℤ)) row.2 col.2 : ℂ) -
    (ρ : ℂ) * (blockC ((row.1.val : ℤ) - (col.1.val : ℤ)) row.2 col.2 : ℂ)

def scaledToeplitz (ρ : ℝ) (n : ℕ) : BlockMatrix n := (80 : ℂ) • toeplitz ρ n

def coefficientA (ρ : ℝ) : ℂ := -(ρ : ℂ) - 6 * Complex.I
def coefficientB (ρ : ℝ) : ℂ := -7 * (ρ : ℂ) - 30 * Complex.I
def coefficientC (ρ : ℝ) : ℂ := 7 * (ρ : ℂ) - 30 * Complex.I
def coefficientD (ρ : ℝ) : ℂ := -25 * (ρ : ℂ) - 30 * Complex.I
def coefficientE (ρ : ℝ) : ℂ := (ρ : ℂ) - 6 * Complex.I
def coefficientF (ρ : ℝ) : ℂ := 25 * (ρ : ℂ) - 30 * Complex.I

def leadingScalar (ρ : ℝ) : ℂ := 30 - (ρ : ℂ) ^ 2 - 10 * Complex.I * (ρ : ℂ)
def middleScalar (ρ : ℝ) : ℂ := 24 * (ρ : ℂ) ^ 2 + 80 * Complex.I * (ρ : ℂ) - 240
def centralScalar (ρ : ℝ) : ℂ := 420 - 46 * (ρ : ℂ) ^ 2

def leadingBlock (ρ : ℝ) : Square 2 :=
  !![coefficientA ρ, coefficientB ρ; coefficientB ρ, coefficientD ρ]

def transferRhs (ρ : ℝ) : Matrix (Fin 2) (Fin 4) ℂ :=
  !![24 * (ρ : ℂ), -96 * Complex.I, -coefficientF ρ, -coefficientC ρ;
    -96 * Complex.I, -24 * (ρ : ℂ), -coefficientC ρ, -coefficientE ρ]

def transferMatrix (ρ : ℝ) : Square 4 :=
  let top := (leadingBlock ρ)⁻¹ * transferRhs ρ
  !![top 0 0, top 0 1, top 0 2, top 0 3;
    top 1 0, top 1 1, top 1 2, top 1 3;
    1, 0, 0, 0;
    0, 1, 0, 0]

def forcingMatrix (ρ : ℝ) : Matrix (Fin 4) (Fin 2) ℂ :=
  let inv := (leadingBlock ρ)⁻¹
  !![inv 0 0, inv 0 1; inv 1 0, inv 1 1; 0, 0; 0, 0]

def boundaryVector : Fin 4 → ℂ := ![1, 0, 0, 0]
def boundaryOuter : Square 4 := fun r s => boundaryVector r * boundaryVector s

/-- Finite zero extension encodes every negative and terminal index without
an unchecked cast or a synthetic boundary correction. -/
def coordinate {n : ℕ} (x : BlockVector n) (j : ℤ) (c : Fin 2) : ℂ :=
  ∑ k : Fin n, if (k.val : ℤ) = j then x (k, c) else 0

def sourceState {n : ℕ} (x : BlockVector n) (j : ℕ) : Fin 4 → ℂ :=
  ![coordinate x (j : ℤ) 0, coordinate x ((j : ℤ) - 1) 1,
    coordinate x ((j : ℤ) - 1) 0, coordinate x ((j : ℤ) - 2) 1]

def numerator (ρ : ℝ) : ℂ[X] :=
  C (leadingScalar ρ) + C (-120 - (ρ : ℂ) ^ 2 + 22 * Complex.I * (ρ : ℂ)) * X +
    C (2 * ((ρ : ℂ) ^ 2 + 18)) * X ^ 2

def denominator (ρ : ℝ) : ℂ[X] :=
  C (leadingScalar ρ) + C (middleScalar ρ) * X + C (centralScalar ρ) * X ^ 2 +
    C (star (middleScalar ρ)) * X ^ 3 + C (star (leadingScalar ρ)) * X ^ 4

def quartic (ρ : ℝ) : ℂ[X] :=
  C (leadingScalar ρ) * X ^ 4 + C (middleScalar ρ) * X ^ 3 +
    C (centralScalar ρ) * X ^ 2 + C (star (middleScalar ρ)) * X +
    C (star (leadingScalar ρ))

def quotientCubic (ρ : ℝ) : ℂ[X] :=
  C (leadingScalar ρ) * X ^ 3 + C (leadingScalar ρ + middleScalar ρ) * X ^ 2 -
    C (star (leadingScalar ρ) + star (middleScalar ρ)) * X - C (star (leadingScalar ρ))

def realCubic (ρ : ℝ) : Cubic ℝ :=
  ⟨6 * (ρ ^ 2 - 10), 25 * ρ, 5 * (ρ ^ 2 - 6), 15 * ρ⟩

def complexCubic (ρ : ℝ) : ℂ[X] := (realCubic ρ).toPoly.map Complex.ofRealHom
def cayley (x : ℂ) : ℂ := (1 + Complex.I * x) / (1 - Complex.I * x)

/-- Four actual distinct, nonzero roots of the explicit quartic. Existence
is a separate required theorem and is never an unproved final hypothesis. -/
def RootData (ρ : ℝ) (roots : Fin 4 → ℂ) : Prop :=
  Function.Injective roots ∧
    (∀ i : Fin 4, roots i ≠ 0 ∧ (quartic ρ).IsRoot (roots i)) ∧
    roots 0 = 1 ∧ ‖roots 1‖ = 1 ∧ ‖roots 2‖ < 1 ∧ 1 < ‖roots 3‖

/-- Lagrange polynomials evaluated at the actual transfer matrix. -/
def spectralProjector (ρ : ℝ) (roots : Fin 4 → ℂ) (i : Fin 4) : Square 4 :=
  Polynomial.aeval (transferMatrix ρ) (Lagrange.basis Finset.univ roots i)

def dominantGamma (ρ : ℝ) (roots : Fin 4 → ℂ) : ℂ := spectralProjector ρ roots 3 0 0
def spectralRemainder (ρ : ℝ) (roots : Fin 4 → ℂ) (j : ℕ) : Square 4 :=
  transferMatrix ρ ^ j - (roots 3 ^ j) • spectralProjector ρ roots 3

def boundaryScalar (ρ : ℝ) (n : ℕ) : ℂ := (transferMatrix ρ ^ n) 0 0
def normalizedBoundary (ρ : ℝ) (roots : Fin 4 → ℂ) (n : ℕ) : ℂ :=
  boundaryScalar ρ n / (dominantGamma ρ roots * roots 3 ^ n)

/-- The first power is guarded by ell<j. Validity is asserted only for
j<=n and ell<n; the formula does not conceal an asymptotic approximation. -/
def greenKernel (ρ : ℝ) (n j ell : ℕ) : Matrix (Fin 4) (Fin 2) ℂ :=
  (if ell < j then transferMatrix ρ ^ (j - 1 - ell) * forcingMatrix ρ else 0) -
    (boundaryScalar ρ n)⁻¹ •
      (transferMatrix ρ ^ j * boundaryOuter *
        transferMatrix ρ ^ (n - 1 - ell) * forcingMatrix ρ)

/-- Candidate inverse for M=80H. Its equality with the true inverse and its
right-inverse identity are mandatory exports, not part of this definition. -/
def inverseCandidate (ρ : ℝ) (n : ℕ) : BlockMatrix n := fun row col =>
  if row.2 = 0 then greenKernel ρ n row.1.val col.1.val 0 col.2
  else greenKernel ρ n (row.1.val + 1) col.1.val 1 col.2

end
end NLA.MF22
