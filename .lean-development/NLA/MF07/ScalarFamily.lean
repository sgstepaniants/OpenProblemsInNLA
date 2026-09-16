/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original scalar endpoint:
Matthew J. Colbrook, University of Cambridge, DAMTP.
-/
import NLA.MF07.RootSemantics

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF07

lemma scalar_matrix_eq_smul_one (A : Square 1) : A = A 0 0 • (1 : Square 1) := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  simp [hi, hj]

lemma scalar_spectralNorm (A : Square 1) : spectralNorm A = ‖A 0 0‖ := by
  calc
    spectralNorm A = spectralNorm (A 0 0 • (1 : Square 1)) := congrArg spectralNorm (scalar_matrix_eq_smul_one A)
    _ = ‖A 0 0‖ := by rw [spectralNorm_smul, spectralNorm_one le_rfl, mul_one]

lemma scalar_spectralNorm_mul (A B : Square 1) :
    spectralNorm (A * B) = spectralNorm A * spectralNorm B := by
  simp [scalar_spectralNorm, Matrix.mul_apply, norm_mul]

lemma scalar_replicate_norm (A : Square 1) (n : ℕ) :
    spectralNorm (matrixProduct (List.replicate n A)) = spectralNorm A ^ n := by
  induction n with
  | zero => simp [spectralNorm_one (d := 1) le_rfl]
  | succ n ih =>
      simp [List.replicate_succ, matrixProduct_cons, scalar_spectralNorm_mul, ih, pow_succ]

lemma scalar_growth_eq (M : Set (Square 1)) (hM : IsCompact M)
    (hne : M.Nonempty) (n : ℕ) : familyGrowth M n = familyNorm M ^ n := by
  apply le_antisymm (family_growth_maximum le_rfl M hM hne n).2.1
  obtain ⟨_, ⟨A, hA, he⟩, _⟩ := family_norm_maximum le_rfl M hM hne
  have hw : WordIn M (List.replicate n A) := by
    intro B hB
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hB
    exact hA
  have h := word_le_familyGrowth M hM n (List.replicate n A)
    (List.length_replicate n A) hw
  simpa only [scalar_replicate_norm, he] using h

lemma scalar_rootGrowth (M : Set (Square 1)) (hM : IsCompact M)
    (hne : M.Nonempty) (n : ℕ) (hn : 1 ≤ n) : rootGrowth M n = familyNorm M := by
  have hL := (family_norm_maximum le_rfl M hM hne).1
  rw [rootGrowth, Real.rpow_eq_pow, scalar_growth_eq M hM hne n, one_div]
  exact Real.pow_rpow_inv_natCast hL (show n ≠ 0 by omega)

theorem scalar_family_growth (M : Set (Square 1)) (hM : IsCompact M)
    (hne : M.Nonempty) :
    (∀ n : ℕ, familyGrowth M n = familyNorm M ^ n) ∧
      jointSpectralRadius M = familyNorm M := by
  refine ⟨scalar_growth_eq M hM hne, ?_⟩
  apply le_antisymm
  · simpa only [scalar_rootGrowth M hM hne 1 le_rfl] using
      jointSpectralRadius_le_root M hM hne 1 le_rfl
  · apply le_csInf (rootValues_nonempty M)
    rintro r ⟨n, hn, rfl⟩
    rw [scalar_rootGrowth M hM hne n hn]

#print axioms scalar_family_growth
#assert_trust kernel scalar_family_growth

end NLA.MF07
