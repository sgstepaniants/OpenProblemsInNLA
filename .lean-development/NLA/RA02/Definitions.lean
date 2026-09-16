/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted statement draft.
Original mathematical resolution: Matthew J. Colbrook, Department of Applied
Mathematics and Theoretical Physics, University of Cambridge.

Definitions only. No normalization, PSD preservation, spectral estimate,
history identity, or counterexample bound is assumed here. All are independent
Challenge obligations. The finite arrowhead route is an alternative to the
retained manuscript's stronger sharp limiting construction.
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev History (n k : ℕ) := Fin k → Fin n

def realTrace {n : ℕ} (A : Square n) : ℝ := A.trace.re

def quadraticValue {n : ℕ} (A : Square n) (x : Fin n → ℂ) : ℝ :=
  (star x ⬝ᵥ (A *ᵥ x)).re

/-- Actual squared Euclidean norm, with no entrywise max norm. -/
def squaredNorm {n : ℕ} (x : Fin n → ℂ) : ℝ := ∑ i, Complex.normSq (x i)

/-- Zero-diagonal choices are harmless totalization. Their probability is zero
for a nonzero PSD residual. The nonzero case is the original complex update. -/
def choleskyStep {n : ℕ} (A : Square n) (j : Fin n) : Square n :=
  if A j j = 0 then A else fun a b => A a b - A a j * A j b / A j j

/-- On a zero PSD residual use uniform dummy labels; all residuals stay zero.
The n=0 value is only totalization: normalization is asserted for n>=1. -/
def pivotMass {n : ℕ} (A : Square n) (j : Fin n) : ℝ :=
  if realTrace A = 0 then 1 / (n : ℝ) else (A j j).re / realTrace A

/-- Chronological residual, including all zero-probability paths. -/
def pathResidual {n : ℕ} (A : Square n) : List (Fin n) → Square n
  | [] => A
  | j :: w => pathResidual (choleskyStep A j) w

/-- Product of actual conditional masses; no independence assumption. -/
def pathWeight {n : ℕ} (A : Square n) : List (Fin n) → ℝ
  | [] => 1
  | j :: w => pivotMass A j * pathWeight (choleskyStep A j) w

def pathContribution {n : ℕ} (A : Square n) (w : List (Fin n)) : ℝ :=
  pathWeight A w * realTrace (pathResidual A w)

/-- Full finite expectation. Every ordered label sequence is included. -/
def expectedTrace {n : ℕ} (A : Square n) (k : ℕ) : ℝ :=
  ∑ f : History n k, pathContribution A (List.ofFn f)

/-- Mathlib's genuinely decreasing eigenvalues. The finite-index transport
uses only card(Fin n)=n; the separately reindexed eigenvalues is not used. -/
def orderedEigenvalues {n : ℕ} (A : Square n) (hA : A.IsHermitian) : Fin n → ℝ :=
  fun i => hA.eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm i)

/-- Zero-based i>=r is the original one-based j>r tail. -/
def rankTail {n : ℕ} (A : Square n) (hA : A.IsHermitian) (r : ℕ) : ℝ :=
  ∑ i ∈ (Finset.univ.filter fun i : Fin n => r ≤ i.val), orderedEigenvalues A hA i

/-- The complete positive assertion in the original RA-02 question. -/
def PolynomialTraceFactor : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ p : ℝ, 0 ≤ p ∧
    ∀ n : ℕ, 1 ≤ n → ∀ A : Square n, ∀ hA : A.PosSemidef,
      ∀ r : ℕ, 1 ≤ r → r ≤ n →
        expectedTrace A r ≤ C * Real.rpow (r : ℝ) p * rankTail A hA.isHermitian r

/-- Exact parameters, never machine-floating-point constants. -/
def smallParameter (r : ℕ) : ℝ := 1 / (2 * (r : ℝ) + 1)
def scaleParameter (r : ℕ) : ℝ := smallParameter r ^ (2 * (r + 1))
def diagonalWeight (r i : ℕ) : ℝ := scaleParameter r ^ i
def couplingWeight (r i : ℕ) : ℝ := smallParameter r ^ (i + 1)

def cornerValue (r : ℕ) (U : Finset (Fin r)) : ℝ :=
  scaleParameter r ^ r + ∑ i ∈ U, diagonalWeight r i.val * couplingWeight r i.val ^ 2

def ordinaryLabels {r : ℕ} (U : Finset (Fin r)) : Finset (Fin (r + 1)) :=
  U.image (fun i : Fin r => i.castSucc)

/-- The two explicit residual shapes, zero-padded in the original label set.
`lastPresent=true` means the distinguished pivot has not been selected. -/
def arrowheadState (r : ℕ) (U : Finset (Fin r)) (lastPresent : Bool) : Square (r + 1) :=
  fun i j =>
    if i ∈ ordinaryLabels U ∧ j ∈ ordinaryLabels U then
      (((if i = j then diagonalWeight r i.val else 0) -
        (if lastPresent then 0 else
          (diagonalWeight r i.val * couplingWeight r i.val) *
            (diagonalWeight r j.val * couplingWeight r j.val) / cornerValue r U)) : ℝ)
    else if lastPresent then
      if i = Fin.last r ∧ j = Fin.last r then (cornerValue r U : ℂ)
      else if i = Fin.last r ∧ j ∈ ordinaryLabels U then
        ((diagonalWeight r j.val * couplingWeight r j.val : ℝ) : ℂ)
      else if j = Fin.last r ∧ i ∈ ordinaryLabels U then
        ((diagonalWeight r i.val * couplingWeight r i.val : ℝ) : ℂ)
      else 0
    else 0

/-- The explicit real-entry complex witness of order r+1. -/
def arrowhead (r : ℕ) : Square (r + 1) := arrowheadState r Finset.univ true

def rayleighProbe (r : ℕ) (i : Fin (r + 1)) : ℂ :=
  if i = Fin.last r then 1 else (-(couplingWeight r i.val) : ℝ)

def remainingOrdinary (r : ℕ) (w : List (Fin (r + 1))) : Finset (Fin r) :=
  Finset.univ.filter fun i => i.castSucc ∉ w

def lastRemaining (r : ℕ) (w : List (Fin (r + 1))) : Bool :=
  !(w.contains (Fin.last r))

/-- Actual chronological prefix traces, including the initial trace. -/
def prefixTraceProduct {n : ℕ} (A : Square n) (w : List (Fin n)) : ℝ :=
  ∏ s : Fin w.length, realTrace (pathResidual A (w.take s.val))

/-- Actual pivot values, with the label at that position read from the list. -/
def pivotProduct {n : ℕ} (A : Square n) (w : List (Fin n)) : ℝ :=
  ∏ s : Fin w.length, ((pathResidual A (w.take s.val)) (w.get s) (w.get s)).re

def commonNumerator (r : ℕ) : ℝ :=
  scaleParameter r ^ r * ∏ i : Fin r, diagonalWeight r i.val

/-- At stage s<r, true chooses the carried label and replaces it by s.
The extension past r is totalization only and is not used in the proof. -/
def carryLabel (r : ℕ) (bits : Fin r → Bool) : ℕ → Fin (r + 1)
  | 0 => Fin.last r
  | s + 1 => if hs : s < r then
      if bits ⟨s, hs⟩ then (⟨s, hs⟩ : Fin r).castSucc else carryLabel r bits s
    else carryLabel r bits s

def retainedHistory (r : ℕ) (bits : Fin r → Bool) : History (r + 1) r :=
  fun s => if bits s then carryLabel r bits s.val else s.castSucc

/-- The full set of binary-encoded histories, not the process's sample space. -/
def retainedHistories (r : ℕ) : Finset (History (r + 1) r) :=
  Finset.univ.image (retainedHistory r)

def retainedPrefix (r : ℕ) (bits : Fin r → Bool) (s : ℕ) : List (Fin (r + 1)) :=
  (List.ofFn (retainedHistory r bits)).take s

def initialLabels (r s : ℕ) : Finset (Fin (r + 1)) :=
  Finset.univ.filter fun j => j.val < s ∨ j = Fin.last r

end
end NLA.RA02
