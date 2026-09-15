/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

DRAFT statement definitions only; no proof implementation is imported.
Mathematical counterexample: Matthew J. Colbrook, Department of Applied
Mathematics and Theoretical Physics, University of Cambridge.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
AI-assisted formalization. Typechecking and independent reviews are pending.
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Topology.Constructions
import Mathlib.Topology.Connected.Basic

set_option autoImplicit false
open scoped BigOperators Classical MatrixOrder
noncomputable section
namespace NLA.PF02

abbrev Mat (k : ℕ) := Matrix (Fin k) (Fin k) ℝ
abbrev Rect (p q : ℕ) := Matrix (Fin p) (Fin q) ℝ

/-- All row and column factors, with the ordinary finite-product Euclidean
matrix topology. No restriction to the two explicit witness tuples is made. -/
abbrev FactorTuple (k p q : ℕ) :=
  (Fin p → Mat k) × (Fin q → Mat k)

/-- Actual real positive semidefinite factors and their ordinary trace products.
Matrix.PosSemidef includes symmetry; no complex factors or entrywise PSD proxy. -/
def IsPSDFactorization {p q k : ℕ} (M : Rect p q)
    (F : FactorTuple k p q) : Prop :=
  (∀ i, (F.1 i).PosSemidef) ∧
  (∀ j, (F.2 j).PosSemidef) ∧
  ∀ i j, (F.1 i * F.2 j).trace = M i j

/-- The COMPLETE fiber, with inherited subspace topology from all factor entries. -/
abbrev FactorizationSpace {p q : ℕ} (k : ℕ) (M : Rect p q) :=
  {F : FactorTuple k p q // IsPSDFactorization M F}

/-- Exact real PSD rank k: existence at k and minimality among every allowed
positive natural size. This is the canonical minimum written without an
arbitrary default value for an empty minimization set. -/
def RealPSDRankEquals {p q : ℕ} (M : Rect p q) (k : ℕ) : Prop :=
  1 ≤ k ∧ Nonempty (FactorizationSpace k M) ∧
    ∀ r : ℕ, 1 ≤ r → Nonempty (FactorizationSpace r M) → k ≤ r

/-- The prescribed real GL(k) primal/dual congruence in the exact source order.
Units of the real square matrix algebra are precisely invertible real matrices. -/
def congruenceTransform {p q k : ℕ} (S : (Mat k)ˣ)
    (F : FactorTuple k p q) : FactorTuple k p q :=
  ((fun i => (S : Mat k).transpose * F.1 i * (S : Mat k)),
   (fun j => ((S⁻¹ : (Mat k)ˣ) : Mat k) * F.2 j *
     (((S⁻¹ : (Mat k)ˣ) : Mat k).transpose)))

/-- Precisely one common real change of basis for every primal/dual factor. -/
def CongruenceRel {p q k : ℕ} {M : Rect p q}
    (F G : FactorizationSpace k M) : Prop :=
  ∃ S : (Mat k)ˣ,
    (G : FactorTuple k p q) = congruenceTransform S (F : FactorTuple k p q)

/-- The full orbit quotient. Mathlib's topology on Quot is the coinduced
quotient topology, not a chosen discrete topology. The relation's equivalence
and preservation of the factorization fiber are separate proof obligations;
thus its generated equivalence classes are exactly the original GL(k) orbits. -/
abbrev FactorizationOrbit {p q : ℕ} (k : ℕ) (M : Rect p q) :=
  Quot (CongruenceRel (k := k) (M := M))

def orbitMk {p q k : ℕ} {M : Rect p q} :
    FactorizationSpace k M → FactorizationOrbit k M := Quot.mk _

/-- Entire original universal statement: all k >= 3, positive row/column
counts, real entrywise nonnegative M, the ORIGINAL ordinary-rank hypothesis,
minimal real PSD factor size, and connectedness of the full quotient topology. -/
def MinimalPSDOrbitConnectedConjecture : Prop :=
  ∀ k p q : ℕ, 3 ≤ k → 1 ≤ p → 1 ≤ q → ∀ M : Rect p q,
    (∀ i j, 0 ≤ M i j) → M.rank = k * (k + 1) / 2 →
      RealPSDRankEquals M k →
        IsConnected (Set.univ : Set (FactorizationOrbit k M))

/-- Colbrook's unchanged integer matrix, interpreted over the reals. -/
def witnessMatrix : Mat 6 :=
  !![24, 20, 20, 16, 16, 16;
     20, 24, 20, 16, 16, 16;
     20, 20, 24, 16, 16, 16;
     16, 16, 16, 14, 12, 12;
     16, 16, 16, 12, 14, 12;
     16, 16, 16, 12, 12, 14]

/-- Six actual 3 by 3 matrices; both primal and dual witness factors use them. -/
def witnessFactors : Fin 6 → Mat 3 :=
  ![!![4, 0, 0; 0, 2, 0; 0, 0, 2],
    !![2, 0, 0; 0, 4, 0; 0, 0, 2],
    !![2, 0, 0; 0, 2, 0; 0, 0, 4],
    !![2, 1, 0; 1, 2, 0; 0, 0, 2],
    !![2, 0, 1; 0, 2, 0; 1, 0, 2],
    !![2, 0, 0; 0, 2, 1; 0, 1, 2]]

/-- Only factor number four (zero-based index 3) is reflected. This is applied
to BOTH primal and dual factors, preserving the same trace-product matrix. -/
def reflectedFactors : Fin 6 → Mat 3 :=
  fun i => if i = 3 then !![2, -1, 0; -1, 2, 0; 0, 0, 2]
    else witnessFactors i

def witnessTuple : FactorTuple 3 6 6 := (witnessFactors, witnessFactors)
def reflectedTuple : FactorTuple 3 6 6 := (reflectedFactors, reflectedFactors)

/-- Original ordered coordinates on the six-dimensional real symmetric space. -/
def symmetricCoordinates (A : Mat 3) : Fin 6 → ℝ :=
  ![A 0 0, A 1 1, A 2 2, A 0 1, A 0 2, A 1 2]

def rowCoordinateMatrix (A : Fin 6 → Mat 3) : Mat 6 :=
  fun i j => symmetricCoordinates (A i) j

def orientationDeterminant (F : FactorTuple 3 6 6) : ℝ :=
  (rowCoordinateMatrix F.1).det

/-- Raw continuous determinant sign on the actual fiber. The value at zero is
irrelevant only AFTER nonvanishing has been proved for EVERY factorization. -/
def orientationSign (F : FactorizationSpace 3 witnessMatrix) : ℝ :=
  if 0 < orientationDeterminant (F : FactorTuple 3 6 6) then 1 else -1

/-- Coordinate basis, with unnormalized symmetric off-diagonal directions. -/
def symmetricCoordinateBasis : Fin 6 → Mat 3 :=
  ![!![1, 0, 0; 0, 0, 0; 0, 0, 0],
    !![0, 0, 0; 0, 1, 0; 0, 0, 0],
    !![0, 0, 0; 0, 0, 0; 0, 0, 1],
    !![0, 1, 0; 1, 0, 0; 0, 0, 0],
    !![0, 0, 1; 0, 0, 0; 1, 0, 0],
    !![0, 0, 0; 0, 0, 1; 0, 1, 0]]

/-- Row-coordinate matrix of X -> S^T X S on the ACTUAL symmetric basis. -/
def congruenceCoordinateMatrix (S : Mat 3) : Mat 6 :=
  fun i j => symmetricCoordinates
    (S.transpose * symmetricCoordinateBasis i * S) j

end NLA.PF02
