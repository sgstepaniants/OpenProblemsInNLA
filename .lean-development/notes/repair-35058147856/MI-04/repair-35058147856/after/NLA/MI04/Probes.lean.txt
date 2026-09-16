/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Two exact diagonal probes isolate one row/column magnitude. The whole finite
sum cancels symbolically, independently of the dimension.
-/
import NLA.MI04.WeightedProbes

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04

def basePeak {n : ℕ} (i : Fin n) : Fin n → ℝ := fun k => if k = i then 1 else 0

def tweakedPeak {n : ℕ} (i j : Fin n) : Fin n → ℝ := fun k =>
  if k = i then 1 else if k = j then (1 : ℝ) / 2 else 0

lemma basePeak_bounds {n : ℕ} (i : Fin n) :
    basePeak i i = 1 ∧ ∀ k, k ≠ i →
      -(1 : ℝ) / 2 ≤ basePeak i k ∧ basePeak i k ≤ (1 : ℝ) / 2 := by
  refine ⟨by simp [basePeak], ?_⟩
  intro k hk
  norm_num [basePeak, hk]

lemma tweakedPeak_bounds {n : ℕ} (i j : Fin n) :
    tweakedPeak i j i = 1 ∧ ∀ k, k ≠ i →
      -(1 : ℝ) / 2 ≤ tweakedPeak i j k ∧ tweakedPeak i j k ≤ (1 : ℝ) / 2 := by
  refine ⟨by simp [tweakedPeak], ?_⟩
  intro k hk
  by_cases hkj : k = j
  · subst k
    norm_num [tweakedPeak, hk]
  · norm_num [tweakedPeak, hk, hkj]

lemma weighted_probe_difference {n : ℕ} (q : Fin n → ℝ) (i j : Fin n) (hji : j ≠ i) :
    (∑ k, q k / (1 + basePeak i k)) -
      (∑ k, q k / (1 + tweakedPeak i j k)) = q j / 3 := by
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ k, (q k / (1 + basePeak i k) - q k / (1 + tweakedPeak i j k))) =
        ∑ k, if k = j then q j / 3 else 0 := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hkj : k = j
      · subst k
        norm_num [basePeak, tweakedPeak, hji] <;> ring
      · by_cases hki : k = i
        · subst k
          simp [basePeak, tweakedPeak, hkj]
        · simp [basePeak, tweakedPeak, hki, hkj]
    _ = q j / 3 := by simp

theorem offDiagonal_magnitude_symmetry {n : ℕ} (hn : 1 ≤ n) (X : Square n)
    (hX : ExtremeSymmetry X) :
    ∀ i j : Fin n, Complex.normSq (X i j) = Complex.normSq (X j i) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  obtain ⟨hbase, hbasebounds⟩ := basePeak_bounds i
  obtain ⟨hprobe, hprobebounds⟩ := tweakedPeak_bounds i j
  have h0 := weighted_magnitude_identity hn X hX i (basePeak i) hbase hbasebounds
  have h1 := weighted_magnitude_identity hn X hX i (tweakedPeak i j) hprobe hprobebounds
  have hrow := weighted_probe_difference (fun k => Complex.normSq (X i k)) i j (Ne.symm hij)
  have hcol := weighted_probe_difference (fun k => Complex.normSq (X k i)) i j (Ne.symm hij)
  rw [h0, h1] at hrow
  linarith

#print axioms offDiagonal_magnitude_symmetry
#assert_trust kernel offDiagonal_magnitude_symmetry

end NLA.MI04
