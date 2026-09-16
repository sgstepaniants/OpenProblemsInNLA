/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Department of Applied
Mathematics and Theoretical Physics, University of Cambridge.

Statement-only definitions. The literal complex GEPP, maxima, and origin
recursions reuse the accepted IE14 source with exact semantic bodies; see
REUSE-AUDIT.json. No bound, valid trajectory, determinant, or sharpness theorem
is assumed in any definition. The only proof terms below discharge Fin bounds.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators Classical NNReal
noncomputable section
namespace NLA.IE13

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev PivotPath (n : ℕ) := Fin n → Fin n

/-- Literal row swaps in the fixed original column ordering. -/
def rowSwap {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  fun i j => S (Equiv.swap k p i) j

/-- Exact Schur update, padded by zero off the new active block. -/
def schurStep {n : ℕ} (S : Mat n) (k p : Fin n) : Mat n :=
  let B := rowSwap S k p
  fun i j => if k < i ∧ k < j then B i j - (B i k / B k k) * B k j else 0

/-- Stage zero is the actual input; no preliminary permutation is performed. -/
def trajectory {n : ℕ} (A : Mat n) (path : PivotPath n) : ℕ → Mat n
  | 0 => A
  | k+1 => if h : k<n then schurStep (trajectory A path k) ⟨k,h⟩ (path ⟨k,h⟩) else 0

def AdmissiblePivot {n : ℕ} (S : Mat n) (k p : Fin n) : Prop :=
  k ≤ p ∧ S p k ≠ 0 ∧ ∀ i, k ≤ i → ‖S i k‖ ≤ ‖S p k‖

/-- Every maximal-modulus tie is permitted. -/
def AdmissiblePath {n : ℕ} (A : Mat n) (path : PivotPath n) : Prop :=
  ∀ k, AdmissiblePivot (trajectory A path k.val) k (path k)

def entryMaxNN {n : ℕ} (A : Mat n) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n => ‖A ij.1 ij.2‖₊)

def entryMax {n : ℕ} (A : Mat n) : ℝ := entryMaxNN A

def activeMaxNN {n : ℕ} (S : Mat n) (k : ℕ) : ℝ≥0 :=
  Finset.univ.sup (fun ij : Fin n × Fin n =>
    if k ≤ ij.1.val ∧ k ≤ ij.2.val then ‖S ij.1 ij.2‖₊ else 0)

def activeMax {n : ℕ} (S : Mat n) (k : ℕ) : ℝ := activeMaxNN S k

/-- All n active stages, including the input and final scalar, enter the numerator. -/
def growth {n : ℕ} (A : Mat n) (path : PivotPath n) : ℝ :=
  ((Finset.univ.sup (fun k : Fin n => activeMaxNN (trajectory A path k.val) k.val) : ℝ≥0) : ℝ) /
    entryMax A

/-- Original input label of a current physical row after the actual swaps. -/
def origin {n : ℕ} (path : PivotPath n) : ℕ → Equiv.Perm (Fin n)
  | 0 => Equiv.refl _
  | k+1 => if h : k<n then
      (Equiv.swap ⟨k,h⟩ (path ⟨k,h⟩)).trans (origin path k)
    else origin path k


/-- Bandwidth at most p below and q above, in the original ordering. -/
def Banded {n : ℕ} (p q : ℕ) (A : Mat n) : Prop :=
  ∀ i j, j.val + p < i.val ∨ i.val + q < j.val → A i j = 0

def BandedInput {n : ℕ} (p q : ℕ) (A : Mat n) : Prop :=
  A.det ≠ 0 ∧ Banded p q A

def PositionsValid {n : ℕ} (path : PivotPath n) : Prop := ∀ k, k ≤ path k

/-- Only actual earlier steps are required by this prefix predicate. -/
def AdmissiblePrefix {n : ℕ} (A : Mat n) (path : PivotPath n) (t : ℕ) : Prop :=
  ∀ k : Fin n, k.val < t → AdmissiblePivot (trajectory A path k.val) k (path k)

def OriginalRowActive {n : ℕ} (path : PivotPath n) (k : ℕ) (i : Fin n) : Prop :=
  k ≤ ((origin path k).symm i).val

def originalRowStage {n : ℕ} (A : Mat n) (path : PivotPath n)
    (k : ℕ) (i j : Fin n) : ℂ :=
  trajectory A path k ((origin path k).symm i) j

def pivotLabel {n : ℕ} (path : PivotPath n) (k : Fin n) : Fin n :=
  origin path k.val (path k)

/-- Surviving original labels strictly before the next fresh band row. -/
def oldRows {n : ℕ} (p : ℕ) (path : PivotPath n) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => OriginalRowActive path k i ∧ i.val < k + p)

/-- Old rows together with the fresh row when it exists; no bound is built in. -/
def frontRows {n : ℕ} (p : ℕ) (path : PivotPath n) (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => OriginalRowActive path k i ∧ i.val ≤ k + p)

/-- Exact recurrence history. Slot r at time t will be proved equal to h_(t-r).
The implementation uses only structural recursion in t. -/
def recurrenceHistory (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | t + 1, r => if r = 0 then
      1 + ∑ s : Fin p, recurrenceHistory p t s.val
    else recurrenceHistory p t (r - 1)

def bandSequence (p t : ℕ) : ℕ := recurrenceHistory p t 0

/-- The source's explicit p-entry envelope, with the initial zero state separate. -/
def envelope (p t : ℕ) (i : Fin p) : ℕ :=
  if t = 0 then 0 else
    1 + ∑ r ∈ Finset.range (p - i.val), bandSequence p (t - (r + 1))

def envelopeSum (p t r : ℕ) : ℕ :=
  ∑ i : Fin p, if i.val < r then envelope p t i else 0

/-- Exact count of envelope updates relevant to a still-active target column.
An early column starts after one imaginary all-ones update. -/
def columnAge {n : ℕ} (p q k : ℕ) (j : Fin n) : ℕ :=
  if j.val < p + q then k + 1 else k - (j.val - (p + q))

def sharpBound (p q : ℕ) : ℝ :=
  if p = 0 then 1 else (bandSequence p (p + q) : ℝ)

/-- All dimensions allowed by the original question, all actual complex inputs,
and all legal GEPP tie paths. -/
def growthValues (p q : ℕ) : Set ℝ :=
  {r | ∃ n : ℕ, 1 + max p q ≤ n ∧ ∃ A : Mat n,
    BandedInput p q A ∧ ∃ path : PivotPath n,
      AdmissiblePath A path ∧ growth A path = r}

def sharpConstant (p q : ℕ) : ℝ := sSup (growthValues p q)

abbrev RatMat (n : ℕ) := Matrix (Fin n) (Fin n) ℚ

def witnessOrder (p q : ℕ) : ℕ := 2 * p + q + 1

def witnessScale (p : ℕ) : ℚ := (1 / 2 : ℚ) ^ p

/-- Unit lower triangular with -1 on the first p subdiagonals. -/
def witnessLowerRational (p q : ℕ) : RatMat (witnessOrder p q) := fun i j =>
  if i = j then 1 else if j.val < i.val ∧ i.val ≤ j.val + p then -1 else 0

/-- Inverse factor-row labeling: the source's sigma is (p+1,1,...,p,p+2,...).
This defines the original matrix; it is not a preliminary algorithmic swap. -/
def witnessFactorIndex (p q : ℕ) (i : Fin (witnessOrder p q)) :
    Fin (witnessOrder p q) :=
  if h : i.val < p then ⟨i.val + 1, by unfold witnessOrder; omega⟩
  else if i.val = p then ⟨0, by unfold witnessOrder; omega⟩ else i

/-- The exact source vector for an early column, now using zero-based indices. -/
def witnessUpperColumn (p q : ℕ) (k i : Fin (witnessOrder p q)) : ℚ :=
  if k.val ≤ p then
    if i.val = 0 then 1 else
      if i.val ≤ k.val then (2 : ℚ) ^ (i.val - 1) else 0
  else if i = k then 1 else 0

/-- Complete rational input in its original ordering, including target and
later identity columns. No invertibility or growth fact is assumed. -/
def witnessRational (p q : ℕ) : RatMat (witnessOrder p q) := fun i j =>
  if j.val < p + q then
    witnessScale p * ∑ r : Fin (witnessOrder p q),
      witnessLowerRational p q (witnessFactorIndex p q i) r * witnessUpperColumn p q j r
  else if j.val = p + q then (if p ≤ i.val then 1 else 0)
  else if i = j then 1 else 0

def witnessMatrix (p q : ℕ) : Mat (witnessOrder p q) :=
  fun i j => (witnessRational p q i j : ℂ)

/-- Physical current-row choices realizing the rotation prefix; validity of
this path's prefix is a theorem obligation, not a definition field. -/
def witnessSeedPath (p q : ℕ) : PivotPath (witnessOrder p q) := fun k =>
  if k.val ≤ p then ⟨p, by unfold witnessOrder; omega⟩ else k

def witnessTarget (p q : ℕ) : Fin (witnessOrder p q) :=
  ⟨p + q, by unfold witnessOrder; omega⟩

end NLA.IE13
