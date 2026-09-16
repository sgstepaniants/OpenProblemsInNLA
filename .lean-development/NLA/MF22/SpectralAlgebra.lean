/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The full actual transfer certificate discharges the sole matrix-specific
premise of the independently implemented Lagrange algebra helper.
-/
import NLA.MF22.ProjectorAlgebra
import NLA.MF22.TransferCertificates

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open scoped BigOperators

theorem spectral_projector_algebra (ρ : ℝ) (hρ : 0 < ρ)
    (roots : Fin 4 → ℂ) (hroots : RootData ρ roots) :
    (∑ i : Fin 4, spectralProjector ρ roots i) = 1 ∧
    (∀ i j : Fin 4,
      spectralProjector ρ roots i * spectralProjector ρ roots j =
        if i = j then spectralProjector ρ roots i else 0) ∧
    ∀ j : ℕ, transferMatrix ρ ^ j =
      ∑ i : Fin 4, (roots i ^ j) • spectralProjector ρ roots i := by
  exact spectral_projector_algebra_of_charpoly ρ hρ roots hroots
    (transfer_polynomial_certificates ρ hρ).1

#assert_trust kernel spectral_projector_algebra
#print axioms spectral_projector_algebra

end NLA.MF22
