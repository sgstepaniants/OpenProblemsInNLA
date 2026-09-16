/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, University of Cambridge DAMTP.
Definitions only; no proof implementation or verification claim.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.JointEigenspace

set_option autoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04

abbrev CMatrix (ι : Type*) := Matrix ι ι ℂ
abbrev Square (n : ℕ) := CMatrix (Fin n)
abbrev CVector (ι : Type*) := EuclideanSpace ℂ ι
abbrev Block (n : ℕ) := CMatrix (Fin n ⊕ Fin n)

section FiniteCoordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual complex Euclidean operator norm, never the default Pi matrix norm. -/
def spectralNorm (M : CMatrix ι) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M‖

/-- Literal real part of the complex Hermitian quadratic form. -/
def realQuadratic (M : CMatrix ι) (v : CVector ι) : ℝ :=
  (inner ℂ v (Matrix.toEuclideanCLM M v)).re

def rayleighValues (M : CMatrix ι) : Set ℝ :=
  {r | ∃ v : CVector ι, ‖v‖ = 1 ∧ r = realQuadratic M v}

/-- The attainment and order properties of this supremum are separate obligations. -/
def topValue (M : CMatrix ι) : ℝ := sSup (rayleighValues M)

def realDiagonal (d : ι → ℝ) : CMatrix ι :=
  Matrix.diagonal (fun j => (d j : ℂ))

def unitarySimilarity (M : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) : CMatrix ι :=
  (U : CMatrix ι).conjTranspose * M * (U : CMatrix ι)

def perturbedDiagonal (d : ι → ℝ) (V : CMatrix ι) (ε : ℝ) : CMatrix ι :=
  realDiagonal d + (ε : ℂ) • V

/-- First-order eigenvector correction used only as an explicit Rayleigh test vector. -/
def correctionVector (d : ι → ℝ) (V : CMatrix ι) (a : ι) : CVector ι :=
  WithLp.toLp 2 (fun j => if j = a then 0 else V j a / ((1 - d j : ℝ) : ℂ))

def secondCoefficient (d : ι → ℝ) (V : CMatrix ι) (a : ι) : ℝ :=
  ∑ j, if j = a then 0 else Complex.normSq (V j a) / (1 - d j)

def upperCoefficient (d : ι → ℝ) (V : CMatrix ι) (a : ι) (ε : ℝ) : ℝ :=
  ∑ j, if j = a then 0 else
    Complex.normSq (V j a) / (1 - d j - ε * spectralNorm V)

end FiniteCoordinates

/-- Literal positive-block completion with off-diagonal X and its adjoint. -/
def completion {n : ℕ} (A X B : Square n) : Block n :=
  Matrix.fromBlocks A X X.conjTranspose B

def pencil {n : ℕ} (X T : Square n) : Block n := completion T X (-T)

/-- The full hypothesis of the permanent canonical problem. -/
def UniversalBlockNorm {n : ℕ} (X : Square n) : Prop :=
  ∀ A B : Square n, A.IsHermitian → B.IsHermitian →
    (completion A X B).PosSemidef →
      spectralNorm (completion A X B) ≤ spectralNorm (A + B)

/-- Full affine-Hermitian representation, allowing alpha=0 and scalar X. -/
def EssentiallyHermitian {n : ℕ} (X : Square n) : Prop :=
  ∃ K : Square n, K.IsHermitian ∧ ∃ α β : ℂ,
    X = α • K + β • (1 : Square n)

/-- Equality of the actual upper extrema of K and -K, for every Hermitian T. -/
def ExtremeSymmetry {n : ℕ} (X : Square n) : Prop :=
  ∀ T : Square n, T.IsHermitian →
    topValue (pencil X T) = topValue (-pencil X T)

def matrixCoefficient {n : ℕ} (X : Square n)
    (u v : CVector (Fin n)) : ℂ := inner ℂ u (Matrix.toEuclideanCLM X v)

def PairMagnitudeSymmetry {n : ℕ} (X : Square n) : Prop :=
  ∀ u v : CVector (Fin n), ‖u‖ = 1 → ‖v‖ = 1 → inner ℂ u v = 0 →
    ‖matrixCoefficient X u v‖ = ‖matrixCoefficient X v u‖

end NLA.MI04
