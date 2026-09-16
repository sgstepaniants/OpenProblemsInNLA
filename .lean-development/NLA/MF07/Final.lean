/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical proof:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The dimension-only constant is chosen before the compact family. The scalar
case is handled separately, so no division by d-1 occurs at d=1.
-/
import NLA.MF07.QuantitativeComparison
import NLA.MF07.ScalarFamily
import NLA.MF07.Numerical

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF07

theorem radius_one_growth {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (hr : jointSpectralRadius M = 1)
    (n : ℕ) (hn : 1 ≤ n) :
    familyGrowth M n ≤ growthConstant d * (familyNorm M * (n : ℝ)) ^ (d - 1) := by
  by_cases hd1 : d = 1
  · subst d
    have hscalar := scalar_family_growth M hM hne
    have hL : familyNorm M = 1 := hscalar.2.symm.trans hr
    rw [hscalar.1 n, hL]
    norm_num [growthConstant]
  · have hd2 : 2 ≤ d := by omega
    have hL : 1 ≤ familyNorm M := (radius_one_semantics hd M hM hne).2 hr
    obtain ⟨hs, hb⟩ := comparison_threshold_bound d n hd2 hn (familyNorm M) hL
    exact (quantitative_comparison hd M hM hne hr
      (comparisonThreshold d n (familyNorm M)) hs n).trans hb

/-- Original full target: arbitrary compact complex families, all words, and
one dimension-only constant chosen before the family and word length. -/
theorem canonical_uniform_bound (d : ℕ) (hd : 1 ≤ d) :
    ∃ Θ : ℝ, 0 < Θ ∧ ∀ M : Set (Square d), IsCompact M → M.Nonempty →
      jointSpectralRadius M = 1 → ∀ n : ℕ, 1 ≤ n → ∀ A : Fin n → Square d,
      (∀ i, A i ∈ M) →
      spectralNorm (finiteProduct A) ≤ Θ * (familyNorm M * (n : ℝ)) ^ (d - 1) := by
  refine ⟨growthConstant d, growth_constant_positive d hd, ?_⟩
  intro M hM hne hr n hn A hA
  have hw : WordIn M (List.ofFn A) := WordIn_ofFn M A hA
  exact (word_le_familyGrowth M hM n (List.ofFn A) List.length_ofFn hw).trans
    (radius_one_growth hd M hM hne hr n hn)

#print axioms radius_one_growth
#assert_trust kernel radius_one_growth
#print axioms canonical_uniform_bound
#assert_trust kernel canonical_uniform_bound

end NLA.MF07
