/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

Literal physical GEPP semantics and attained finite maxima. The genuine input,
every active stage, and the final scalar all enter the frozen growth definition.
-/
import NLA.IE13.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators NNReal
namespace NLA.IE13

theorem gepp_model_semantics {n : ℕ} (A : Mat n) (path : PivotPath n) :
    trajectory A path 0 = A ∧
    ∀ k i j : Fin n,
      trajectory A path (k.val + 1) i j =
        if k < i ∧ k < j then
          trajectory A path k.val (Equiv.swap k (path k) i) j -
            (trajectory A path k.val (Equiv.swap k (path k) i) k /
              trajectory A path k.val (path k) k) *
            trajectory A path k.val (path k) j
        else 0 := by
  refine ⟨rfl, ?_⟩
  intro k i j
  simp only [trajectory, dif_pos k.isLt, schurStep, rowSwap,
    Equiv.swap_apply_left]

lemma entryMax_pos_of_det_ne_zero {n : ℕ} (hn : 1 ≤ n) (A : Mat n)
    (hA : A.det ≠ 0) : 0 < entryMax A := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  by_contra hpos
  have hmax : entryMax A = 0 := le_antisymm (le_of_not_gt hpos) (entryMax_nonneg A)
  have hz : A = 0 := by
    ext i j
    apply norm_eq_zero.mp
    exact le_antisymm (hmax ▸ norm_le_entryMax A i j) (norm_nonneg _)
  exact hA (by simp [hz])

theorem entryMax_semantics {n : ℕ} (hn : 1 ≤ n) (A : Mat n) :
    0 ≤ entryMax A ∧ (∀ i j, ‖A i j‖ ≤ entryMax A) ∧
    (∃ i j, ‖A i j‖ = entryMax A) ∧ (A.det ≠ 0 → 0 < entryMax A) := by
  obtain ⟨h0, hbound, i, j, hmax⟩ := entryMax_attained_basic hn A
  exact ⟨h0, hbound, ⟨i, j, hmax.symm⟩, entryMax_pos_of_det_ne_zero hn A⟩

theorem activeMax_semantics {n : ℕ} (S : Mat n) (k : Fin n) :
    0 ≤ activeMax S k.val ∧
    (∀ i j, k ≤ i → k ≤ j → ‖S i j‖ ≤ activeMax S k.val) ∧
    ∃ i j, k ≤ i ∧ k ≤ j ∧ ‖S i j‖ = activeMax S k.val := by
  classical
  refine ⟨activeMax_nonneg S k.val,
    fun i j hi hj => norm_le_activeMax S k.val i j hi hj, ?_⟩
  let s : Finset (Fin n × Fin n) :=
    Finset.univ.filter (fun ij => k ≤ ij.1 ∧ k ≤ ij.2)
  have hs : s.Nonempty := ⟨(k, k), by simp [s]⟩
  obtain ⟨ij, hij, hmax⟩ := Finset.exists_max_image s
    (fun ij => ‖S ij.1 ij.2‖₊) hs
  have hactive : k ≤ ij.1 ∧ k ≤ ij.2 := (Finset.mem_filter.mp hij).2
  have hupper : activeMaxNN S k.val ≤ ‖S ij.1 ij.2‖₊ := by
    unfold activeMaxNN
    apply Finset.sup_le
    intro ab _
    by_cases hab : k.val ≤ ab.1.val ∧ k.val ≤ ab.2.val
    · rw [if_pos hab]
      exact hmax ab (by simpa [s] using hab)
    · rw [if_neg hab]
      exact bot_le
  have hlower : ‖S ij.1 ij.2‖ ≤ activeMax S k.val :=
    norm_le_activeMax S k.val ij.1 ij.2 hactive.1 hactive.2
  refine ⟨ij.1, ij.2, hactive.1, hactive.2, le_antisymm hlower ?_⟩
  exact NNReal.coe_le_coe.mpr hupper

lemma peakMax_attained {n : ℕ} (hn : 1 ≤ n) (A : Mat n) (path : PivotPath n) :
    ∃ k : Fin n, activeMax (trajectory A path k.val) k.val = peakMax A path := by
  classical
  let z : Fin n := ⟨0, by omega⟩
  obtain ⟨k, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun k => activeMaxNN (trajectory A path k.val) k.val) ⟨z, Finset.mem_univ z⟩
  refine ⟨k, le_antisymm (activeMax_le_peakMax A path k) ?_⟩
  exact NNReal.coe_le_coe.mpr (Finset.sup_le hmax)

lemma growth_mul_entryMax {n : ℕ} (hn : 1 ≤ n) (A : Mat n)
    (hA : A.det ≠ 0) (path : PivotPath n) :
    growth A path * entryMax A = peakMax A path := by
  change (peakMax A path / entryMax A) * entryMax A = peakMax A path
  exact div_mul_cancel₀ _ (entryMax_pos_of_det_ne_zero hn A hA).ne'

theorem growth_semantics {n : ℕ} (hn : 1 ≤ n) (A : Mat n)
    (hA : A.det ≠ 0) (path : PivotPath n) :
    1 ≤ growth A path ∧
    (∀ k i j : Fin n, k ≤ i → k ≤ j →
      ‖trajectory A path k.val i j‖ ≤ growth A path * entryMax A) ∧
    ∃ k i j : Fin n, k ≤ i ∧ k ≤ j ∧
      ‖trajectory A path k.val i j‖ = growth A path * entryMax A := by
  have hpos := entryMax_pos_of_det_ne_zero hn A hA
  have hproduct := growth_mul_entryMax hn A hA path
  refine ⟨?_, ?_, ?_⟩
  · change 1 ≤ peakMax A path / entryMax A
    apply (le_div_iff₀ hpos).mpr
    simpa only [one_mul] using entryMax_le_peakMax hn A path
  · intro k i j hi hj
    rw [hproduct]
    exact (norm_le_activeMax _ _ i j hi hj).trans (activeMax_le_peakMax A path k)
  · obtain ⟨k, hk⟩ := peakMax_attained hn A path
    obtain ⟨i, j, hi, hj, he⟩ := (activeMax_semantics (trajectory A path k.val) k).2.2
    exact ⟨k, i, j, hi, hj, he.trans (hk.trans hproduct.symm)⟩

#print axioms gepp_model_semantics
#assert_trust kernel gepp_model_semantics
#print axioms entryMax_semantics
#assert_trust kernel entryMax_semantics
#print axioms activeMax_semantics
#assert_trust kernel activeMax_semantics
#print axioms growth_semantics
#assert_trust kernel growth_semantics

end NLA.IE13
