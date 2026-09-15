/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization draft.

Mathematical proof note: George Stepaniants. The optimized cubic is due to
Chen and Chow; prior constant-factor complexity results are due to Cheon,
Kim and Kim. This file contains mathematical definitions, not proof bodies.
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.Sign
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic

set_option autoImplicit false

namespace NLA.MF02

open Polynomial

noncomputable section

/-- The exact two closed intervals in the canonical scalar polynomial model. -/
def gapDomain (δ : ℝ) : Set ℝ := Set.Icc (-1) (-δ) ∪ Set.Icc δ 1

/-- All free real linear combinations of the currently stored polynomials. -/
def freeSpan (registers : List ℝ[X]) : Submodule ℝ ℝ[X] :=
  Submodule.span ℝ {p | p ∈ registers}

/-- A history of product gates retaining every previously stored value.
Each operand can be any free linear combination of all preceding registers.
A product involving a constant does not require a gate: its value already
belongs to `freeSpan`. Permitting a redundant gate does not enlarge an
at-most-budget computation class. -/
inductive ProductHistory : ℕ → List ℝ[X] → Prop where
  | initial : ProductHistory 0 [1, X]
  | product {k : ℕ} {registers : List ℝ[X]} {a b : ℝ[X]}
      (history : ProductHistory k registers)
      (ha : a ∈ freeSpan registers) (hb : b ∈ freeSpan registers) :
      ProductHistory (k + 1) ((a * b) :: registers)

/-- The polynomials computable using at most `m` nonscalar multiplications,
starting from 1 and X, with free real linear combinations and value reuse. -/
def ProgramComputable (m : ℕ) (p : ℝ[X]) : Prop :=
  ∃ k : ℕ, k ≤ m ∧ ∃ registers : List ℝ[X],
    ProductHistory k registers ∧ p ∈ freeSpan registers

/-- One permitted cubic stage, with unrestricted real coefficients. -/
def cubic (a b : ℝ) : ℝ[X] := C a * X + C b * X ^ 3

/-- Exactly `T` cubic stages, including degenerate linear or zero stages.
The empty composition is X. A successor applies its new stage last. -/
inductive CubicComposition : ℕ → ℝ[X] → Prop where
  | empty : CubicComposition 0 X
  | stage {T : ℕ} {p : ℝ[X]} (previous : CubicComposition T p)
      (a b : ℝ) :
      CubicComposition (T + 1) (C a * p + C b * p ^ 3)

/-- The ordinary maximum error, expressed as a real supremum.
For 0 < δ < 1 the image is nonempty and bounded and the maximum is attained;
the Challenge requires that fact explicitly. Real.sign has its usual values
-1, 0, 1; the domain under consideration excludes 0. -/
def uniformError (δ : ℝ) (p : ℝ[X]) : ℝ :=
  sSup ((fun x : ℝ => |p.eval x - Real.sign x|) '' gapDomain δ)

/-- Infimum over the full unrestricted arithmetic-program class. -/
def unrestrictedError (m : ℕ) (δ : ℝ) : ℝ :=
  sInf (uniformError δ '' {p : ℝ[X] | ProgramComputable m p})

/-- Infimum over all real coefficients of exactly T cubic stages. -/
def cubicError (T : ℕ) (δ : ℝ) : ℝ :=
  sInf (uniformError δ '' {p : ℝ[X] | CubicComposition T p})

/-- The canonical minimum stage count, with infimum of the empty set equal
to infinity. No artificial fallback to zero or assumed optimizer is used. -/
def stageMinimum (m : ℕ) (δ : ℝ) : WithTop ℕ :=
  sInf ((fun T : ℕ => (T : WithTop ℕ)) ''
    {T : ℕ | cubicError T δ ≤ unrestrictedError m δ})

def gapRatio (a : ℝ) : ℝ := (1 - a) / (1 + a)

def cubicA (a : ℝ) : ℝ := 1 + a + a ^ 2

/-- 2 A^(3/2)/(3 sqrt(3)), written with A sqrt(A) to avoid real exponents. -/
def cubicScale (a : ℝ) : ℝ :=
  2 * cubicA a * Real.sqrt (cubicA a) / (3 * Real.sqrt 3)

/-- The Chen-Chow scaled cubic. -/
def optimizedCubic (a : ℝ) : ℝ[X] :=
  cubic (cubicA a / cubicScale a) (-1 / cubicScale a)

/-- The common endpoint value of the optimized cubic on [a,1]. -/
def improvedGap (a : ℝ) : ℝ := a * (1 + a) / cubicScale a

end
end NLA.MF02
