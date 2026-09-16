/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original mathematical argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Arbitrary compact families are retained. The finite product parameter space is
(Fin n -> M), whose coordinates range over the entire, possibly infinite family.
-/
import NLA.MF07.MatrixBasics
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF07

lemma wordNorms_eq_range {d : ℕ} (M : Set (Square d)) (n : ℕ) :
    wordNorms M n = Set.range (fun A : Fin n → M =>
      spectralNorm (finiteProduct (fun i => (A i).val))) := by
  ext r
  constructor
  · rintro ⟨w, hw, hM, rfl⟩
    subst n
    let A : Fin w.length → M := fun i => ⟨w.get i, hM _ (List.get_mem w i)⟩
    refine ⟨A, ?_⟩
    simp [finiteProduct, A, List.ofFn_get]
  · rintro ⟨A, rfl⟩
    exact ⟨List.ofFn (fun i => (A i).val), List.length_ofFn,
      WordIn_ofFn M _ (fun i => (A i).property), rfl⟩

lemma wordNorms_nonempty {d : ℕ} (M : Set (Square d)) (hne : M.Nonempty) (n : ℕ) :
    (wordNorms M n).Nonempty := by
  obtain ⟨A, hA⟩ := hne
  rw [wordNorms_eq_range]
  exact ⟨_, ⟨fun _ => ⟨A, hA⟩, rfl⟩⟩

lemma wordNorms_compact {d : ℕ} (M : Set (Square d)) (hM : IsCompact M) (n : ℕ) :
    IsCompact (wordNorms M n) := by
  letI : CompactSpace M := isCompact_iff_compactSpace.mp hM
  rw [wordNorms_eq_range]
  apply isCompact_range
  exact continuous_spectralNorm.comp
    (continuous_finiteProduct.comp (continuous_pi fun i =>
      (continuous_apply i).subtype_val))

theorem family_norm_maximum {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) :
    0 ≤ familyNorm M ∧ (∃ A ∈ M, spectralNorm A = familyNorm M) ∧
      ∀ A ∈ M, spectralNorm A ≤ familyNorm M := by
  have hc : IsCompact (spectralNorm '' M) := hM.image continuous_spectralNorm
  have he : (spectralNorm '' M).Nonempty := hne.image spectralNorm
  obtain ⟨A, hA, hval⟩ := hc.sSup_mem he
  have hmax : ∀ B ∈ M, spectralNorm B ≤ familyNorm M := by
    intro B hB
    exact le_csSup hc.bddAbove ⟨B, hB, rfl⟩
  refine ⟨?_, ⟨A, hA, hval⟩, hmax⟩
  change 0 ≤ sSup (spectralNorm '' M)
  rw [← hval]
  exact spectralNorm_nonneg A

lemma familyGrowth_attained {d : ℕ} (M : Set (Square d)) (hM : IsCompact M)
    (hne : M.Nonempty) (n : ℕ) :
    ∃ w : List (Square d), w.length = n ∧ WordIn M w ∧
      spectralNorm (matrixProduct w) = familyGrowth M n := by
  obtain ⟨w, hw, hword, he⟩ :=
    (wordNorms_compact M hM n).sSup_mem (wordNorms_nonempty M hne n)
  exact ⟨w, hw, hword, he.symm⟩

lemma word_le_familyGrowth {d : ℕ} (M : Set (Square d)) (hM : IsCompact M)
    (n : ℕ) (w : List (Square d)) (hw : w.length = n) (hword : WordIn M w) :
    spectralNorm (matrixProduct w) ≤ familyGrowth M n := by
  exact le_csSup (wordNorms_compact M hM n).bddAbove ⟨w, hw, hword, rfl⟩

lemma familyGrowth_nonneg {d : ℕ} (M : Set (Square d)) (hM : IsCompact M)
    (hne : M.Nonempty) (n : ℕ) : 0 ≤ familyGrowth M n := by
  obtain ⟨w, _, _, he⟩ := familyGrowth_attained M hM hne n
  rw [← he]
  exact spectralNorm_nonneg _

theorem family_growth_maximum {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (n : ℕ) :
    0 ≤ familyGrowth M n ∧ familyGrowth M n ≤ familyNorm M ^ n ∧
    (∃ w : List (Square d), w.length = n ∧ WordIn M w ∧
      spectralNorm (matrixProduct w) = familyGrowth M n) ∧
    ∀ w : List (Square d), w.length = n → WordIn M w →
      spectralNorm (matrixProduct w) ≤ familyGrowth M n := by
  obtain ⟨hL, _, hb⟩ := family_norm_maximum hd M hM hne
  have ha := familyGrowth_attained M hM hne n
  refine ⟨familyGrowth_nonneg M hM hne n, ?_, ha, word_le_familyGrowth M hM n⟩
  obtain ⟨w, hw, hword, he⟩ := ha
  rw [← he, ← hw]
  exact word_spectralNorm_le_pow hd M _ hL hb w hword

lemma familyGrowth_zero {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) : familyGrowth M 0 = 1 := by
  obtain ⟨w, hw, _, he⟩ := familyGrowth_attained M hM hne 0
  have hw0 : w = [] := List.length_eq_zero_iff.mp hw
  simpa [hw0, spectralNorm_one hd] using he.symm

lemma familyGrowth_one {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) : familyGrowth M 1 = familyNorm M := by
  apply le_antisymm
  · simpa using (family_growth_maximum hd M hM hne 1).2.1
  · obtain ⟨_, ⟨A, hA, he⟩, _⟩ := family_norm_maximum hd M hM hne
    rw [← he]
    simpa using word_le_familyGrowth M hM 1 [A] rfl
      ((WordIn_cons_iff M A []).mpr ⟨hA, WordIn_nil M⟩)

theorem family_growth_submultiplicative {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : IsCompact M) (hne : M.Nonempty) (m n : ℕ) :
    familyGrowth M (m + n) ≤ familyGrowth M m * familyGrowth M n := by
  obtain ⟨w, hw, hword, he⟩ := familyGrowth_attained M hM hne (m+n)
  have hu : (w.take m).length = m := by simp [List.length_take, hw]
  have hv : (w.drop m).length = n := by simp [List.length_drop, hw]
  have hsplit : WordIn M (w.take m) ∧ WordIn M (w.drop m) :=
    (WordIn_append_iff M _ _).mp (by simpa using hword)
  have hleft := word_le_familyGrowth M hM m (w.take m) hu hsplit.1
  have hright := word_le_familyGrowth M hM n (w.drop m) hv hsplit.2
  rw [← he, ← List.take_append_drop m w, matrixProduct_append]
  calc
    spectralNorm (matrixProduct (w.drop m) * matrixProduct (w.take m)) ≤
        spectralNorm (matrixProduct (w.drop m)) * spectralNorm (matrixProduct (w.take m)) :=
      spectralNorm_mul_le _ _
    _ ≤ familyGrowth M n * familyGrowth M m :=
      mul_le_mul hright hleft (spectralNorm_nonneg _) (familyGrowth_nonneg M hM hne n)
    _ = familyGrowth M m * familyGrowth M n := mul_comm _ _

#print axioms family_norm_maximum
#assert_trust kernel family_norm_maximum
#print axioms family_growth_maximum
#assert_trust kernel family_growth_maximum
#print axioms family_growth_submultiplicative
#assert_trust kernel family_growth_submultiplicative

end NLA.MF07
