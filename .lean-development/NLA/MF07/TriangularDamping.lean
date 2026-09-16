/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original triangular damping argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

Reveal one diagonal weight at a time. Each step is a convex combination of two
unitary conjugations. An upper entry survives only when the relevant weights
are equal; arbitrary full equal-weight blocks are therefore retained.
-/
import NLA.MF07.UnitaryGeometry

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF07

/-- Keep the first k+1 weights and extend the last of them constantly. -/
def clippedWeights {d : ℕ} (h : Fin d → ℝ) (k : ℕ) (hk : k < d) (i : Fin d) : ℝ :=
  if i.val ≤ k then h i else h ⟨k, hk⟩

lemma clippedWeights_zero {d : ℕ} (h : Fin d → ℝ) (hd : 0 < d) (i : Fin d) :
    clippedWeights h 0 hd i = h ⟨0, hd⟩ := by
  by_cases hi : i.val ≤ 0
  · have he : i = ⟨0, hd⟩ := Fin.ext (by
      simpa only [Fin.val_mk] using Nat.eq_zero_of_le_zero hi)
    simp [clippedWeights, he]
  · simp [clippedWeights, hi]

lemma clippedWeights_succ_apply {d : ℕ} (h : Fin d → ℝ) (k : ℕ)
    (hk : k+1 < d) (i : Fin d) :
    clippedWeights h (k+1) hk i = if i.val ≤ k then h i else h ⟨k+1, hk⟩ := by
  by_cases hi : i.val ≤ k
  · simp [clippedWeights, hi, show i.val ≤ k+1 by omega]
  · by_cases hi' : i.val ≤ k+1
    · have he : i = ⟨k+1, hk⟩ := Fin.ext (by
        simpa only [Fin.val_mk] using (show i.val = k+1 by omega))
      simp [clippedWeights, he]
    · simp [clippedWeights, hi, hi']

lemma clippedDamping_zero {d : ℕ} (h : Fin d → ℝ) (hd : 0 < d)
    (hpos : ∀ i, 0 < h i) (X : Square d) :
    diagonalDamping (clippedWeights h 0 hd) X = X := by
  have hp : (h ⟨0, hd⟩ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos ⟨0, hd⟩).ne'
  ext i j
  rw [diagonalDamping_apply, clippedWeights_zero, clippedWeights_zero]
  push_cast
  field_simp

lemma clippedDamping_step {d : ℕ} (h : Fin d → ℝ) (hh : Antitone h)
    (hpos : ∀ i, 0 < h i) (X : Square d) (hX : LowerForWeights h X)
    (k : ℕ) (hk : k+1 < d) :
    diagonalDamping (clippedWeights h (k+1) hk) X =
      cutDamping (k+1) (h ⟨k+1, hk⟩ / h ⟨k, by omega⟩)
        (diagonalDamping (clippedWeights h k (by omega)) X) := by
  let ik : Fin d := ⟨k, by omega⟩
  let ik1 : Fin d := ⟨k+1, hk⟩
  have hp : (h ik : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos ik).ne'
  have hp1 : (h ik1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos ik1).ne'
  -- Expose the clipped indices in the complex nonzero facts used for cancellation.
  dsimp only [ik, ik1] at hp hp1
  ext i j
  rw [cutDamping_apply]
  simp only [diagonalDamping_apply, clippedWeights_succ_apply]
  have hpi : (h i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos i).ne'
  have hpj : (h j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos j).ne'
  by_cases hi : i.val ≤ k
  · have hi' : i.val < k+1 := by omega
    by_cases hj : j.val ≤ k
    · have hj' : j.val < k+1 := by omega
      simp [clippedWeights, hi, hj, hi', hj']
    · have hj' : ¬ j.val < k+1 := by omega
      by_cases hstrict : h j < h i
      · simp [clippedWeights, hi, hj, hi', hj', hX i j hstrict]
      · have hki : h ik ≤ h i := hh (show i ≤ ik by exact hi)
        have hjk1 : h j ≤ h ik1 := hh (show ik1 ≤ j by change k+1 ≤ j.val; omega)
        have hk1k : h ik1 ≤ h ik := hh (show ik ≤ ik1 by change k ≤ k+1; omega)
        have he : h ik1 = h ik := by linarith
        have he' : h ⟨k+1, hk⟩ = h ⟨k, by omega⟩ := he
        simp [clippedWeights, hi, hj, hi', hj', he', hp]
  · have hi' : ¬ i.val < k+1 := by omega
    by_cases hj : j.val ≤ k
    · have hj' : j.val < k+1 := by omega
      simp only [clippedWeights, if_neg hi, if_pos hj, if_neg (by simp [hi', hj'] :
        ¬ (i.val < k+1 ↔ j.val < k+1))]
      push_cast
      field_simp [hp, hpj] <;> ring
    · have hj' : ¬ j.val < k+1 := by omega
      simp only [clippedWeights, if_neg hi, if_neg hj, if_pos (by simp [hi', hj'] :
        (i.val < k+1 ↔ j.val < k+1)), one_mul]
      push_cast
      field_simp [hp, hp1] <;> ring

lemma clippedDamping_bound {d : ℕ} (h : Fin d → ℝ) (hh : Antitone h)
    (hpos : ∀ i, 0 < h i) (X : Square d) (hX : LowerForWeights h X) :
    ∀ k : ℕ, ∀ hk : k < d,
      spectralNorm (diagonalDamping (clippedWeights h k hk) X) ≤ spectralNorm X := by
  intro k
  induction k with
  | zero =>
      intro hk
      rw [clippedDamping_zero h hk hpos]
  | succ k ih =>
      intro hk
      have hk0 : k < d := by omega
      have hr0 : 0 ≤ h ⟨k+1, hk⟩ / h ⟨k, hk0⟩ :=
        div_nonneg (hpos _).le (hpos _).le
      have hr1 : h ⟨k+1, hk⟩ / h ⟨k, hk0⟩ ≤ 1 := by
        apply (div_le_one (hpos _)).mpr
        exact hh (show (⟨k, hk0⟩ : Fin d) ≤ ⟨k+1, hk⟩ by change k ≤ k+1; omega)
      rw [clippedDamping_step h hh hpos X hX k hk]
      exact (cutDamping_spectralNorm_le (k+1) _ hr0 hr1 _).trans (ih hk0)

theorem triangular_damping {d : ℕ} (h : Fin d → ℝ) (hh : Antitone h)
    (hpos : ∀ i, 0 < h i) (X : Square d) (hX : LowerForWeights h X) :
    spectralNorm (diagonalDamping h X) ≤ spectralNorm X := by
  by_cases hd : d = 0
  · subst d
    have he : diagonalDamping h X = X := Subsingleton.elim _ _
    rw [he]
  · have hk : d-1 < d := by omega
    have he : clippedWeights h (d-1) hk = h := by
      funext i
      simp [clippedWeights, show i.val ≤ d-1 by omega]
    simpa only [he] using clippedDamping_bound h hh hpos X hX (d-1) hk

#print axioms triangular_damping
#assert_trust kernel triangular_damping

end NLA.MF07
