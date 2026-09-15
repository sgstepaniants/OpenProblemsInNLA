/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA.

Mathematical counterexample: Matthew J. Colbrook, Department of Applied
Mathematics and Theoretical Physics, University of Cambridge.
AI-assisted statement draft. No proof implementation or verification claim.
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace NLA.SP04

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
abbrev MatrixPolynomial (n : ℕ) := MvPolynomial (Fin n × Fin n) ℝ
abbrev Parameters := (Fin 3 → ℝ) × (Fin 3 → ℝ) × (Fin 3 → ℝ)

/-- The ordinary finite product norm supplies the ambient differential calculus.
The optimization objective below still explicitly uses the Frobenius norm. -/
instance normedAddCommGroupMat (n : ℕ) : NormedAddCommGroup (Mat n) :=
  Matrix.normedAddCommGroup

instance normedSpaceMat (n : ℕ) : NormedSpace ℝ (Mat n) :=
  Matrix.normedSpace

/-- Mathlib's actual Frobenius norm, selected explicitly rather than the
ambient function-space sup norm. -/
def frobeniusNorm {n : ℕ} (A : Mat n) : ℝ :=
  letI : NormedAddCommGroup (Mat n) := Matrix.frobeniusNormedAddCommGroup
  ‖A‖

def frobeniusDistance {n : ℕ} (U X : Mat n) : ℝ := frobeniusNorm (U - X)

def UnitAbsoluteDeterminant {n : ℕ} (X : Mat n) : Prop := |X.det| = 1

/-- The complete original real stationary equation, including both signs of det X. -/
def StationaryPair {n : ℕ} (U X : Mat n) (c : ℝ) : Prop :=
  UnitAbsoluteDeterminant X ∧ X.transpose * (U - X) = c • (1 : Mat n)

/-- Minimum is among every real stationary pair, not only diagonal candidates. -/
def LeastAbsoluteMultiplier {n : ℕ} (U X : Mat n) (c : ℝ) : Prop :=
  StationaryPair U X c ∧
  ∀ (Y : Mat n) (d : ℝ), StationaryPair U Y d → |c| ≤ |d|

/-- Ties are excluded by equality of the entire stationary pair. -/
def UniqueLeastAbsoluteMultiplier {n : ℕ} (U X : Mat n) (c : ℝ) : Prop :=
  LeastAbsoluteMultiplier U X c ∧
  ∀ (Y : Mat n) (d : ℝ), StationaryPair U Y d → |d| ≤ |c| → Y = X ∧ d = c

/-- Global nearestness over the full feasible set, expressed without a default infimum. -/
def IsNearest {n : ℕ} (U X : Mat n) : Prop :=
  UnitAbsoluteDeterminant X ∧
  ∀ Y : Mat n, UnitAbsoluteDeterminant Y →
    frobeniusDistance U X ≤ frobeniusDistance U Y

/-- Both inverse identities are explicit; this is the ordinary real orthogonal group. -/
def Orthogonal {n : ℕ} (P : Mat n) : Prop :=
  P.transpose * P = 1 ∧ P * P.transpose = 1

/-- The precise strict singular-value box from the retained counterexample. -/
def OrderedBox (s : Fin 3 → ℝ) : Prop :=
  7 / 4 < s 0 ∧ s 0 < s 1 ∧ s 1 < s 2 ∧ s 2 < 44 / 25

/-- An actual orthogonal decomposition with positive distinct singular values
in the source's box, not an assumption that generic data are diagonal. -/
def InSourceSpectralBox (U : Mat 3) : Prop :=
  ∃ (s : Fin 3 → ℝ) (P Q : Mat 3),
    OrderedBox s ∧ Orthogonal P ∧ Orthogonal Q ∧
    U = P * Matrix.diagonal s * Q.transpose

/-- This includes an actual improving feasible matrix and a unique global
minimum absolute multiplier, as required even on the optional unique-choice locus. -/
def Counterexample (U : Mat 3) : Prop :=
  InSourceSpectralBox U ∧
  ∃ (X : Mat 3) (c : ℝ) (Y : Mat 3),
    UniqueLeastAbsoluteMultiplier U X c ∧ UnitAbsoluteDeterminant Y ∧
    frobeniusDistance U Y < frobeniusDistance U X

/-- A real polynomial in every matrix entry. -/
def polynomialValue {n : ℕ} (p : MatrixPolynomial n) (U : Mat n) : ℝ :=
  MvPolynomial.eval (fun ij => U ij.1 ij.2) p

/-- The usual real algebraic sets: common zero loci of families of real
polynomials in all n² entries. The family can be infinite. -/
def IsRealAlgebraicSet {n : ℕ} (Z : Set (Mat n)) : Prop :=
  ∃ F : Set (MatrixPolynomial n),
    Z = {U | ∀ p ∈ F, polynomialValue p U = 0}

/-- The generic nearestness rule, allowing an arbitrary proper real algebraic
exceptional set in each dimension and restricting to unique choices as permitted
by the source. Refuting this weaker unique-choice version refutes the full rule. -/
def GenericNearestRule : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    ∃ Z : Set (Mat n), IsRealAlgebraicSet Z ∧ Z ≠ Set.univ ∧
      ∀ U : Mat n, U ∉ Z →
        ∀ (X : Mat n) (c : ℝ),
          UniqueLeastAbsoluteMultiplier U X c → IsNearest U X

/-- Large and small roots for the positive multiplier equation x²-sx+c=0. -/
def positiveLargeRoot (s c : ℝ) : ℝ := (s + Real.sqrt (s ^ 2 - 4 * c)) / 2

def positiveSmallRoot (s c : ℝ) : ℝ := (s - Real.sqrt (s ^ 2 - 4 * c)) / 2

/-- Positive root and negative-root magnitude for x²-sx-t=0. -/
def positiveNegativeCaseRoot (s t : ℝ) : ℝ :=
  (s + Real.sqrt (s ^ 2 + 4 * t)) / 2

def negativeRootMagnitude (s t : ℝ) : ℝ :=
  (Real.sqrt (s ^ 2 + 4 * t) - s) / 2

/-- Absolute product of the pattern with only the first root negative. -/
def selectedProduct (s : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  negativeRootMagnitude (s 0) t *
    positiveNegativeCaseRoot (s 1) t * positiveNegativeCaseRoot (s 2) t

/-- Each Boolean selects the negative root; the product covers all eight patterns. -/
def negativePattern (s : Fin 3 → ℝ) (t : ℝ) (e : Fin 3 → Bool) : Fin 3 → ℝ :=
  fun i => if e i then -negativeRootMagnitude (s i) t
    else positiveNegativeCaseRoot (s i) t

def firstNegativePattern : Fin 3 → Bool := ![true, false, false]

def selectedMatrix (s : Fin 3 → ℝ) (t : ℝ) : Mat 3 :=
  Matrix.diagonal (negativePattern s t firstNegativePattern)

/-- The competing feasible matrix changes only the first diagonal sign. -/
def improvingMatrix (s : Fin 3 → ℝ) (t : ℝ) : Mat 3 :=
  Matrix.diagonal ![negativeRootMagnitude (s 0) t,
    positiveNegativeCaseRoot (s 1) t, positiveNegativeCaseRoot (s 2) t]

def rationalCos (t : ℝ) : ℝ := (1 - t ^ 2) / (1 + t ^ 2)
def rationalSin (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)

def rotation01 (t : ℝ) : Mat 3 :=
  !![rationalCos t, rationalSin t, 0;
     -rationalSin t, rationalCos t, 0;
     0, 0, 1]

def rotation02 (t : ℝ) : Mat 3 :=
  !![rationalCos t, 0, rationalSin t;
     0, 1, 0;
     -rationalSin t, 0, rationalCos t]

def rotation12 (t : ℝ) : Mat 3 :=
  !![1, 0, 0;
     0, rationalCos t, rationalSin t;
     0, -rationalSin t, rationalCos t]

def rotations (a : Fin 3 → ℝ) : Mat 3 :=
  rotation01 (a 0) * rotation02 (a 1) * rotation12 (a 2)

/-- A nine-real-dimensional map into every entry of a real 3×3 matrix. -/
def orthogonalChart (z : Parameters) : Mat 3 :=
  rotations z.2.1 * Matrix.diagonal z.1 * (rotations z.2.2).transpose

def centerSingularValues : Fin 3 → ℝ := ![1751 / 1000, 1755 / 1000, 1759 / 1000]
def chartCenter : Parameters := (centerSingularValues, 0, 0)
def chartDomain : Set Parameters := {z | OrderedBox z.1}

/-- Exact derivative at zero rotation angles. The theorem must prove it is
an invertible continuous linear map; no inverse-function hypothesis is assumed. -/
def chartDerivativeFormula (s : Fin 3 → ℝ) (h : Parameters) : Mat 3 :=
  !![h.1 0, 2 * s 1 * h.2.1 0 - 2 * s 0 * h.2.2 0,
       2 * s 2 * h.2.1 1 - 2 * s 0 * h.2.2 1;
     -2 * s 0 * h.2.1 0 + 2 * s 1 * h.2.2 0, h.1 1,
       2 * s 2 * h.2.1 2 - 2 * s 1 * h.2.2 2;
     -2 * s 0 * h.2.1 1 + 2 * s 2 * h.2.2 1,
       -2 * s 1 * h.2.1 2 + 2 * s 2 * h.2.2 2, h.1 2]

end NLA.SP04
