/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical resolution:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The explicit vector cancels every ordinary square. These exact energy and
norm identities do not substitute an artificial definition for the spectrum.
-/
import NLA.RA02.ArrowheadQuadratic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.RA02
noncomputable section
open scoped BigOperators ComplexOrder Matrix

@[simp] lemma rayleighProbe_last (r : ℕ) : rayleighProbe r (Fin.last r) = 1 := by
  simp [rayleighProbe]

@[simp] lemma rayleighProbe_ordinary (r : ℕ) (i : Fin r) :
    rayleighProbe r i.castSucc = (-(couplingWeight r i.val) : ℝ) := by
  simp [rayleighProbe]

lemma rayleighProbe_ne_zero (r : ℕ) : rayleighProbe r ≠ 0 := by
  intro h
  have he := congrFun h (Fin.last r)
  simpa using he

lemma rayleighProbe_energy (r : ℕ) :
    quadraticValue (arrowhead r) (rayleighProbe r) = scaleParameter r ^ r := by
  rw [arrowhead_quadratic]
  simp

lemma rayleighProbe_squaredNorm (r : ℕ) :
    squaredNorm (rayleighProbe r) = 1 + ∑ i : Fin r, couplingWeight r i.val ^ 2 := by
  rw [squaredNorm, Fin.sum_univ_castSucc]
  simp [pow_two, add_comm]

theorem rayleigh_probe_values (r : ℕ) :
    rayleighProbe r ≠ 0 ∧
    quadraticValue (arrowhead r) (rayleighProbe r) = scaleParameter r ^ r ∧
    squaredNorm (rayleighProbe r) = 1 + (∑ i : Fin r, couplingWeight r i.val ^ 2) ∧
    1 ≤ squaredNorm (rayleighProbe r) := by
  refine ⟨rayleighProbe_ne_zero r, rayleighProbe_energy r, rayleighProbe_squaredNorm r, ?_⟩
  rw [rayleighProbe_squaredNorm]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => sq_nonneg _)

#print axioms rayleigh_probe_values
#assert_trust kernel rayleigh_probe_values

end
end NLA.RA02
