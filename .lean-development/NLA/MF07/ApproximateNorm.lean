/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical construction:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The proved root limit bounds every discounted word, including the finite initial
segment. The actual product-envelope construction then provides the norm.
-/
import NLA.MF07.RootSemantics
import NLA.MF07.ProductEnvelope

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Topology
open Filter

noncomputable section
namespace NLA.MF07

lemma exponential_growth_envelope {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (hr : jointSpectralRadius M = 1)
    (a : ℝ) (ha : 1 < a) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, familyGrowth M n ≤ K * a ^ n := by
  have hlim := radius_one_root_limit hd M hM hne hr
  have hL : 1 ≤ familyNorm M := (radius_one_semantics hd M hM hne).2 hr
  have hL0 : 0 ≤ familyNorm M := le_trans zero_le_one hL
  have htail : ∀ᶠ n : ℕ in atTop, rootGrowth M n < a :=
    hlim.eventually (gt_mem_nhds ha)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp htail
  have hK : 1 ≤ familyNorm M ^ N := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one hL N
  refine ⟨familyNorm M ^ N, hK, ?_⟩
  intro n
  have ha0 : 0 ≤ a := by linarith
  have han : 1 ≤ a ^ n := by
    simpa only [one_pow] using pow_le_pow_left₀ zero_le_one ha.le n
  by_cases hn0 : n = 0
  · simpa [hn0, familyGrowth_zero hd M hM hne] using hK
  · have hn1 : 1 ≤ n := by omega
    by_cases hnN : N ≤ n
    · have hp : familyGrowth M n ≤ a ^ n := by
        rw [← rootGrowth_pow M hM hne n hn1]
        exact pow_le_pow_left₀ (rootGrowth_nonneg M hM hne n) (hN n hnN).le n
      exact hp.trans (by nlinarith [pow_nonneg ha0 n])
    · have hng : familyGrowth M n ≤ familyNorm M ^ n :=
        (family_growth_maximum hd M hM hne n).2.1
      have hp : familyNorm M ^ n ≤ familyNorm M ^ N :=
        pow_le_pow_right₀ hL (by omega)
      exact (hng.trans hp).trans (by nlinarith [pow_nonneg hL0 N])

theorem approximate_extremal_norm {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (hr : jointSpectralRadius M = 1)
    (a : ℝ) (ha : 1 < a) :
    ∃ v : EuclideanVector d → ℝ, ∃ c : ℝ, 1 ≤ c ∧ IsComplexNorm v ∧
      (∀ x, ‖x‖ ≤ v x ∧ v x ≤ c * ‖x‖) ∧
      ∀ A ∈ M, ∀ x, v (applyMatrix A x) ≤ a * v x := by
  obtain ⟨K, hK, hbound⟩ := exponential_growth_envelope hd M hM hne hr a ha
  have ha0 : 0 < a := by linarith
  have hword : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map (fun A => A))) ≤ K * a ^ z.length := by
    intro z hz
    simpa using (word_le_familyGrowth M hM z.length z rfl hz).trans (hbound z.length)
  refine ⟨productEnvelope M (fun A => A) a, K, hK,
    productEnvelope_isComplexNorm M (fun A => A) a K ha0 hword,
    productEnvelope_bounds M (fun A => A) a K ha0 hword, ?_⟩
  intro A hA x
  exact productEnvelope_generator M (fun A => A) a K ha0 hword A hA x

#print axioms approximate_extremal_norm
#assert_trust kernel approximate_extremal_norm

end NLA.MF07
