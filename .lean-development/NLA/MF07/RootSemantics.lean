/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Fekete's actual logarithmic theorem proves the forward root limit. The converse
uses repeated blocks and the original root limit, including zero-growth cases;
positivity is not added as an assumption on a family.
-/
import NLA.MF07.CompactGrowth
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped Topology
open Filter

noncomputable section
namespace NLA.MF07

lemma rootGrowth_nonneg {d : ℕ} (M : Set (Square d)) (hM : IsCompact M)
    (hne : M.Nonempty) (n : ℕ) : 0 ≤ rootGrowth M n :=
  Real.rpow_nonneg (familyGrowth_nonneg M hM hne n) _

lemma rootValues_nonempty {d : ℕ} (M : Set (Square d)) :
    {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = rootGrowth M n}.Nonempty :=
  ⟨rootGrowth M 1, 1, le_rfl, rfl⟩

lemma rootValues_bddBelow {d : ℕ} (M : Set (Square d)) (hM : IsCompact M)
    (hne : M.Nonempty) : BddBelow {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = rootGrowth M n} := by
  refine ⟨0, ?_⟩
  rintro r ⟨n, _, rfl⟩
  exact rootGrowth_nonneg M hM hne n

lemma jointSpectralRadius_le_root {d : ℕ} (M : Set (Square d)) (hM : IsCompact M)
    (hne : M.Nonempty) (n : ℕ) (hn : 1 ≤ n) : jointSpectralRadius M ≤ rootGrowth M n :=
  csInf_le (rootValues_bddBelow M hM hne) ⟨n, hn, rfl⟩

lemma rootGrowth_pow {d : ℕ} (M : Set (Square d)) (hM : IsCompact M)
    (hne : M.Nonempty) (n : ℕ) (hn : 1 ≤ n) :
    rootGrowth M n ^ n = familyGrowth M n := by
  simpa only [rootGrowth, Real.rpow_eq_pow, one_div] using
    Real.rpow_inv_natCast_pow (familyGrowth_nonneg M hM hne n) (show n ≠ 0 by omega)

lemma familyGrowth_ge_one_of_radius_one {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (hr : jointSpectralRadius M = 1)
    (n : ℕ) : 1 ≤ familyGrowth M n := by
  by_cases hn : n = 0
  · simp [hn, familyGrowth_zero hd M hM hne]
  · have hn1 : 1 ≤ n := by omega
    have hroot : 1 ≤ rootGrowth M n := by
      rw [← hr]
      exact jointSpectralRadius_le_root M hM hne n hn1
    have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hroot n
    simpa only [one_pow, rootGrowth_pow M hM hne n hn1] using hp

lemma logarithmic_growth_subadditive {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (hr : jointSpectralRadius M = 1) :
    Subadditive (fun n => Real.log (familyGrowth M n)) := by
  have hp (n : ℕ) : 0 < familyGrowth M n :=
    lt_of_lt_of_le zero_lt_one (familyGrowth_ge_one_of_radius_one hd M hM hne hr n)
  intro m n
  calc
    Real.log (familyGrowth M (m+n)) ≤ Real.log (familyGrowth M m * familyGrowth M n) :=
      Real.log_le_log (hp (m+n)) (family_growth_submultiplicative hd M hM hne m n)
    _ = Real.log (familyGrowth M m) + Real.log (familyGrowth M n) :=
      Real.log_mul (hp m).ne' (hp n).ne'

lemma radius_one_root_limit {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (hr : jointSpectralRadius M = 1) :
    Tendsto (rootGrowth M) atTop (𝓝 1) := by
  have hg := familyGrowth_ge_one_of_radius_one hd M hM hne hr
  have hp (n : ℕ) : 0 < familyGrowth M n := lt_of_lt_of_le zero_lt_one (hg n)
  let hsub := logarithmic_growth_subadditive hd M hM hne hr
  have hquot (n : ℕ) : 0 ≤ Real.log (familyGrowth M n) / (n : ℝ) :=
    div_nonneg (Real.log_nonneg (hg n)) (Nat.cast_nonneg n)
  have hb : BddBelow (Set.range (fun n : ℕ => Real.log (familyGrowth M n) / (n : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro r ⟨n, rfl⟩
    exact hquot n
  have hl := hsub.tendsto_lim hb
  have hl0 : 0 ≤ hsub.lim := ge_of_tendsto hl (Filter.Eventually.of_forall hquot)
  have hroot (n : ℕ) : rootGrowth M n = Real.exp (Real.log (familyGrowth M n) / (n : ℝ)) := by
    rw [rootGrowth, Real.rpow_eq_pow, Real.rpow_def_of_pos (hp n)]
    congr 1
    ring
  have he_upper : Real.exp hsub.lim ≤ jointSpectralRadius M := by
    apply le_csInf (rootValues_nonempty M)
    rintro r ⟨n, hn, rfl⟩
    rw [hroot]
    exact Real.exp_le_exp.mpr (hsub.lim_le_div hb (show n ≠ 0 by omega))
  have he : Real.exp hsub.lim = 1 := by
    apply le_antisymm
    · simpa [hr] using he_upper
    · exact Real.one_le_exp_iff.mpr hl0
  have hconv := Real.continuous_exp.continuousAt.tendsto.comp hl
  simpa only [Function.comp_def, he, ← hroot] using hconv

lemma familyGrowth_mul_le_pow {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (k n : ℕ) :
    familyGrowth M (k*n) ≤ familyGrowth M n ^ k := by
  induction k with
  | zero => simp [familyGrowth_zero hd M hM hne]
  | succ k ih =>
      rw [Nat.succ_mul, pow_succ]
      exact (family_growth_submultiplicative hd M hM hne (k*n) n).trans
        (mul_le_mul_of_nonneg_right ih (familyGrowth_nonneg M hM hne n))

lemma rootGrowth_mul_le {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (k n : ℕ) (hk : 1 ≤ k) (hn : 1 ≤ n) :
    rootGrowth M (k*n) ≤ rootGrowth M n := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  calc
    rootGrowth M (k*n) ≤ Real.rpow (familyGrowth M n ^ k) (1 / ((k*n : ℕ) : ℝ)) :=
      Real.rpow_le_rpow (familyGrowth_nonneg M hM hne (k*n))
        (familyGrowth_mul_le_pow hd M hM hne k n) (by positivity)
    _ = rootGrowth M n := by
      -- Normalize the explicit rpow wrapper before applying the public Pow API.
      simp only [rootGrowth, Real.rpow_eq_pow]
      rw [← Real.rpow_natCast_mul (familyGrowth_nonneg M hM hne n)]
      congr 1
      push_cast
      field_simp [hk0, hn0]

lemma one_le_rootGrowth_of_limit {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty)
    (hlim : Tendsto (rootGrowth M) atTop (𝓝 1)) (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ rootGrowth M n := by
  have hmult : Tendsto (fun k : ℕ => k*n) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    refine Filter.eventually_atTop.2 ⟨b, ?_⟩
    intro k hk
    exact hk.trans (by nlinarith)
  have hsubseq := hlim.comp hmult
  apply le_of_tendsto hsubseq
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
  exact rootGrowth_mul_le hd M hM hne k n hk hn

lemma radius_one_of_root_limit {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty)
    (hlim : Tendsto (rootGrowth M) atTop (𝓝 1)) : jointSpectralRadius M = 1 := by
  apply le_antisymm
  · apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact jointSpectralRadius_le_root M hM hne n hn
  · apply le_csInf (rootValues_nonempty M)
    rintro r ⟨n, hn, rfl⟩
    exact one_le_rootGrowth_of_limit hd M hM hne hlim n hn

theorem radius_one_semantics {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) :
    (jointSpectralRadius M = 1 ↔ Tendsto (rootGrowth M) atTop (𝓝 1)) ∧
    (jointSpectralRadius M = 1 → 1 ≤ familyNorm M) := by
  refine ⟨⟨radius_one_root_limit hd M hM hne, radius_one_of_root_limit hd M hM hne⟩, ?_⟩
  intro hr
  simpa only [familyGrowth_one hd M hM hne] using
    familyGrowth_ge_one_of_radius_one hd M hM hne hr 1

lemma identity_word_product {d : ℕ} (z : List (Square d))
    (hz : WordIn ({1} : Set (Square d)) z) : matrixProduct z = 1 := by
  induction z with
  | nil => simp
  | cons A z ih =>
      obtain ⟨hA, hz⟩ := (WordIn_cons_iff _ A z).mp hz
      have hA1 : A = 1 := Set.mem_singleton_iff.mp hA
      simp [hA1, ih hz]

theorem identity_family_semantics {d : ℕ} (hd : 1 ≤ d) :
    familyNorm ({1} : Set (Square d)) = 1 ∧
    (∀ n : ℕ, familyGrowth ({1} : Set (Square d)) n = 1) ∧
    jointSpectralRadius ({1} : Set (Square d)) = 1 := by
  have hM : IsCompact ({1} : Set (Square d)) := isCompact_singleton
  have hne : ({1} : Set (Square d)).Nonempty := Set.singleton_nonempty 1
  have hg (n : ℕ) : familyGrowth ({1} : Set (Square d)) n = 1 := by
    obtain ⟨z, _, hz, he⟩ := familyGrowth_attained _ hM hne n
    simpa [identity_word_product z hz, spectralNorm_one hd] using he.symm
  refine ⟨?_, hg, ?_⟩
  · simp [familyNorm, spectralNorm_one hd]
  · apply radius_one_of_root_limit hd _ hM hne
    have he : rootGrowth ({1} : Set (Square d)) = fun _ => 1 := by
      funext n
      simp [rootGrowth, hg n]
    rw [he]
    exact tendsto_const_nhds

#print axioms radius_one_semantics
#assert_trust kernel radius_one_semantics
#print axioms identity_family_semantics
#assert_trust kernel identity_family_semantics

end NLA.MF07
