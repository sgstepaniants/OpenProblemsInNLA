/-
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. Apache 2.0; AI-assisted.
A Cartesian open box and Mathlib polynomial funext avoid a separate degree argument.
-/
import NLA.SP04.Definitions
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option leancert.trust "kernel"
noncomputable section
namespace NLA.SP04

theorem polynomial_escape (V : Set (Mat 3)) (hV : IsOpen V) (hne : V.Nonempty)
    (p : MatrixPolynomial 3) (hp : p ≠ 0) :
    ∃ U ∈ V, polynomialValue p U ≠ 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  obtain ⟨A, hA⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV A hA
  apply hp
  apply MvPolynomial.funext_set
    (fun ij : Fin 3 × Fin 3 => Set.Ioo (A ij.1 ij.2 - r) (A ij.1 ij.2 + r))
    (fun ij => Set.Ioo_infinite (by linarith))
  intro x hx
  rw [map_zero]
  let U : Mat 3 := fun i j => x (i,j)
  have hU : U ∈ V := by
    apply hball
    change dist U A < r
    apply (dist_pi_lt_iff hr).mpr
    intro i
    apply (dist_pi_lt_iff hr).mpr
    intro j
    have hij := hx (i,j) (Set.mem_univ _)
    change A i j - r < x (i,j) ∧ x (i,j) < A i j + r at hij
    change dist (x (i,j)) (A i j) < r
    rw [Real.dist_eq]
    exact abs_lt.mpr ⟨by linarith [hij.1], by linarith [hij.2]⟩
  simpa only [polynomialValue, U] using hnone U hU

lemma open_set_escapes_algebraic (V : Set (Mat 3)) (hV : IsOpen V) (hne : V.Nonempty)
    (Z : Set (Mat 3)) (hZ : IsRealAlgebraicSet Z) (hproper : Z ≠ Set.univ) :
    ∃ U ∈ V, U ∉ Z := by
  classical
  obtain ⟨A, hA⟩ := (Set.ne_univ_iff_exists_notMem Z).mp hproper
  obtain ⟨F, rfl⟩ := hZ
  change ¬ ∀ p ∈ F, polynomialValue p A = 0 at hA
  push_neg at hA
  obtain ⟨p, hpF, hpA⟩ := hA
  have hp : p ≠ 0 := by
    intro hzero
    rw [hzero] at hpA
    exact hpA (by simp only [polynomialValue, map_zero])
  obtain ⟨U, hUV, hUp⟩ := polynomial_escape V hV hne p hp
  refine ⟨U, hUV, ?_⟩
  intro hUF
  exact hUp (hUF p hpF)

#assert_trust kernel polynomial_escape
#print axioms polynomial_escape
end NLA.SP04
