/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

AI-assisted formalization of Matthew J. Colbrook's IE-17 counterexample.
Formalization affiliation: Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA.
Original mathematics: Matthew J. Colbrook, Department of Applied Mathematics
and Theoretical Physics, University of Cambridge.

UNREVIEWED STATEMENT DRAFT. No proof implementation has begun. This file must
pass non-root Linux type checking and two independent statement reviews before
its bytes are frozen. No local theorem, certificate, or Challenge is imported.
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Span.Basic

set_option autoImplicit false
open scoped BigOperators Classical Matrix.Norms.L2Operator
noncomputable section

namespace NLA.IE17

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- The genuine Euclidean vector norm, not the function-space supremum norm. -/
def euclideanNorm {n : ℕ} (x : Vec n) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖

/-- Exact squared-coordinate sum, to be related to euclideanNorm by a theorem. -/
def normSq {n : ℕ} (x : Vec n) : ℝ := ∑ i, (x i) ^ 2

def realDot {n : ℕ} (x y : Vec n) : ℝ := ∑ i, x i * y i

def outer {m n : ℕ} (x : Vec m) (y : Vec n) : Mat m n := fun i j => x i * y j

/-- Matrix.Norms.L2Operator fixes the induced Euclidean operator norm here.
This is neither the entrywise maximum nor the Frobenius matrix norm. -/
def spectralNorm {m n : ℕ} (E : Mat m n) : ℝ := ‖E‖

def residual {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) : Vec m :=
  b - A.mulVec x

def normalResidual {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) : Vec n :=
  A.transpose.mulVec (residual A b x)

/-- Undamped, zero-start Krylov space span{g,Hg,...,H^(k-1)g}, H=AᵀA,
g=Aᵀb. For k=0 the generating range is empty and the span is {0}. -/
def krylovSpace {m n : ℕ} (A : Mat m n) (b : Vec m) (k : ℕ) :
    Submodule ℝ (Vec n) :=
  Submodule.span ℝ (Set.range fun j : Fin k =>
    ((A.transpose * A) ^ j.val).mulVec (A.transpose.mulVec b))

/-- Exact LSMR as defined in the canonical problem: minimize the Euclidean
normal-residual norm on the Krylov space; among ties take minimum Euclidean
length. Neither floating-point recurrence nor a different residual objective
is substituted. Membership plus the two universal clauses express actual
optimization over every real Krylov vector. -/
def IsLSMRIterate {m n : ℕ} (A : Mat m n) (b : Vec m) (k : ℕ) (x : Vec n) : Prop :=
  x ∈ krylovSpace A b k ∧
  (∀ y ∈ krylovSpace A b k,
    euclideanNorm (normalResidual A b x) ≤ euclideanNorm (normalResidual A b y)) ∧
  (∀ y ∈ krylovSpace A b k,
    euclideanNorm (normalResidual A b y) = euclideanNorm (normalResidual A b x) →
      euclideanNorm x ≤ euclideanNorm y)

/-- A pair of successive nonzero iterates, with the first still before exact
termination. If an earlier Krylov iterate terminated, normal-residual
minimality on nested spaces would force the first residual here to be zero.
The second iterate is permitted to be the exact least-squares solution. -/
def SuccessiveNonzeroIterates {m n : ℕ} (A : Mat m n) (b : Vec m)
    (k : ℕ) (x y : Vec n) : Prop :=
  1 ≤ k ∧ IsLSMRIterate A b k x ∧ IsLSMRIterate A b (k + 1) y ∧
  x ≠ 0 ∧ y ≠ 0 ∧ normalResidual A b x ≠ 0

/-- The actual matrix-only perturbed normal equations with b held fixed.
All real m×n matrices E are allowed, including rank-changing perturbations. -/
def FeasiblePerturbation {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n)
    (E : Mat m n) : Prop :=
  (A + E).transpose.mulVec ((A + E).mulVec x - b) = 0

def feasibleNorms {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) : Set ℝ :=
  {c | ∃ E : Mat m n, FeasiblePerturbation A b x E ∧ c = spectralNorm E}

/-- The full optimization-defined spectral error. A separate theorem must
prove the set is nonempty, bounded below and attains this infimum, so a
strict pointwise certificate cannot exploit a totalized/default infimum.
In particular E=-A is feasible, and at an exact solution E=0 is feasible. -/
def backwardError {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) : ℝ :=
  sInf (feasibleNorms A b x)

/-- The canonical augmented matrix K=[A; (‖r‖₂/‖x‖₂) I]. Sum indexing
represents the vertical concatenation without reindexing finite dimensions. -/
def augmentedMatrix {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    Matrix (Fin m ⊕ Fin n) (Fin n) ℝ :=
  fun i j => Sum.elim (fun i => A i j)
    (fun i => if i = j then euclideanNorm (residual A b x) / euclideanNorm x else 0) i

/-- The Gram-inverse formula is a candidate value for the actual Moore-Penrose
inverse. All four Penrose identities and Gram invertibility are mandatory
exported obligations when x and r are nonzero; no arbitrary inverse replaces it. -/
def augmentedPseudoinverse {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) :
    Matrix (Fin n) (Fin m ⊕ Fin n) ℝ :=
  let K := augmentedMatrix A b x
  (K.transpose * K)⁻¹ * K.transpose

def Penrose {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (K : Matrix ι κ ℝ) (J : Matrix κ ι ℝ) : Prop :=
  K * J * K = K ∧ J * K * J = J ∧
  (K * J).transpose = K * J ∧ (J * K).transpose = J * K

/-- The original projected augmented residual, divided by ‖x‖₂, with the
canonical exact-solution convention. Cases x=0 are outside compared iterates.
The rational normal-equation expression is not used as this definition. -/
def projectionError {m n : ℕ} (A : Mat m n) (b : Vec m) (x : Vec n) : ℝ :=
  if normalResidual A b x = 0 then 0 else
    let K := augmentedMatrix A b x
    let J := augmentedPseudoinverse A b x
    let v : Fin m ⊕ Fin n → ℝ := Sum.elim (residual A b x) (fun _ => 0)
    ‖(WithLp.toLp 2 ((K * J).mulVec v) : EuclideanSpace ℝ (Fin m ⊕ Fin n))‖ /
      euclideanNorm x

/-- Both original universal monotonicity claims, over arbitrary real A and b.
The witness below has full column rank, but that is not added as a restriction
on these conjectures. All minimum-length and stopping conventions are inside
SuccessiveNonzeroIterates and IsLSMRIterate. -/
def SpectralMonotonicity : Prop :=
  ∀ m n : ℕ, ∀ A : Mat m n, ∀ b : Vec m, ∀ k : ℕ, ∀ x y : Vec n,
    SuccessiveNonzeroIterates A b k x y → backwardError A b y ≤ backwardError A b x

def ProjectionMonotonicity : Prop :=
  ∀ m n : ℕ, ∀ A : Mat m n, ∀ b : Vec m, ∀ k : ℕ, ∀ x y : Vec n,
    SuccessiveNonzeroIterates A b k x y → projectionError A b y ≤ projectionError A b x

/-- Colbrook's exact 4×3 witness; the zero fourth row is explicitly allowed. -/
def witnessA : Mat 4 3 := !![1,0,0; 0,6,0; 0,0,5; 0,0,0]
def witnessB : Vec 4 := ![11,1,1,1]
def witnessX1 : Vec 3 := (1 / 31201 : ℝ) • ![11231,6126,5105]
def witnessX2 : Vec 3 := (1 / 55219 : ℝ) • ![87659,7599,16865]
def witnessX3 : Vec 3 := ![11,1/6,1/5]
def witnessW : Vec 4 := ![250,-1,1,27]
def upperCutoff : ℝ := 1979 / 2000

def upperH : ℝ := realDot witnessW (witnessA.mulVec witnessX1)
def upperC0 : Vec 4 := residual witnessA witnessB witnessX1 -
  (realDot witnessW (residual witnessA witnessB witnessX1) / normSq witnessW) • witnessW
def upperA0 : Vec 3 := -witnessA.transpose.mulVec witnessW +
  (upperH / normSq witnessX1) • witnessX1

/-- Fully rational completion from source §4. The norm claim and feasibility
are separate theorem obligations; no completion lemma is assumed as an axiom. -/
def upperPerturbation : Mat 4 3 :=
  (-(normSq witnessW)⁻¹) • (outer witnessW witnessW * witnessA) +
  (normSq witnessX1)⁻¹ • outer upperC0 witnessX1 +
  (upperH / (normSq witnessW * normSq witnessX1 * upperCutoff - upperH ^ 2)) •
    outer upperC0 upperA0

/-- Source lower-bound matrix D, using exact squared sums. -/
def lowerD : Mat 4 4 :=
  (normSq witnessX2)⁻¹ •
    (normSq (residual witnessA witnessB witnessX2) • (1 : Mat 4 4) -
      outer (residual witnessA witnessB witnessX2) (residual witnessA witnessB witnessX2) +
      outer (witnessA.mulVec witnessX2) (witnessA.mulVec witnessX2))

def lowerConvexMatrix : Mat 4 4 :=
  (5 / 6 : ℝ) • (witnessA * witnessA.transpose) + (1 / 6 : ℝ) • lowerD

/-- Integer positive-definiteness certificate, not a replacement for the
optimization-defined backward error. Its exact matrix identity is exported. -/
def lowerIntegerMatrix : Mat 4 4 :=
  !![206417059721, -50293465200, 1125984433750, -1435003762500;
     -50293465200, 83658415217471, 206242965000, -26574143750;
     1125984433750, 206242965000, 61800032332121, 80360210700;
     -1435003762500, -26574143750, 80360210700, 11170189945871]

end NLA.IE17
