/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization of Matthew J. Colbrook's SF-01 result, Cambridge DAMTP.

Thin adapters to Sidney Holden's unchanged Apache-2.0 IV03 formalization.
The positive weight is an explicit premise here; these helpers do not assume
the still-to-be-proved equivalence with the canonical spectral M predicate.
-/
import NLA.SF01.Definitions
import NLA.IV03.Proof

set_option autoImplicit false

namespace NLA.SF01
noncomputable section
open scoped Matrix

lemma weightedZ_maximum_principle {n : ℕ} (C : Square n) (v y : Vector n)
    (hZ : IsZMatrix C) (hv : PositiveWeight C v)
    (hy : ∀ i, 0 ≤ (C *ᵥ y) i) : ∀ i, 0 ≤ y i := by
  exact NLA.IV03.zMatrix_maximum_principle C v y hZ hv.1 hv.2 hy

lemma weightedZ_isUnit {n : ℕ} (C : Square n) (v : Vector n)
    (hZ : IsZMatrix C) (hv : PositiveWeight C v) : IsUnit C := by
  exact NLA.IV03.zMatrix_isUnit C v hZ hv.1 hv.2

lemma weightedZ_inverse_nonnegative {n : ℕ} (C : Square n) (v : Vector n)
    (hZ : IsZMatrix C) (hv : PositiveWeight C v) : ∀ i j, 0 ≤ C⁻¹ i j := by
  exact NLA.IV03.zMatrix_inverse_nonnegative C v hZ hv.1 hv.2

lemma weightedZ_weightVector_equation {n : ℕ} (C : Square n) (v : Vector n)
    (hZ : IsZMatrix C) (hv : PositiveWeight C v) :
    C *ᵥ weightVector C = (fun _ => 1) := by
  have hC := weightedZ_isUnit C v hZ hv
  rw [weightVector, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv C ((Matrix.isUnit_iff_isUnit_det C).mp hC), Matrix.one_mulVec]

end
end NLA.SF01
