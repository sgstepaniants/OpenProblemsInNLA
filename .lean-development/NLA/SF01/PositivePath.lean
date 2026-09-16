/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, Cambridge DAMTP.

A finite maximum and the intermediate value theorem exclude a zero boundary.
This helper has no matrix or spectral assumptions hidden in a definition.
-/
import NLA.SF01.Definitions
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

set_option autoImplicit false

namespace NLA.SF01
noncomputable section

lemma continuous_positive_coordinates {n : ℕ} (hn : 1 ≤ n) (w : ℝ → Vector n)
    (hw : ContinuousOn w (Set.Icc (0 : ℝ) 1))
    (hzero : ∀ i, 0 < w 0 i)
    (hboundary : ∀ t ∈ Set.Icc (0 : ℝ) 1, (∀ i, 0 ≤ w t i) → ∀ i, w t i ≠ 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i, 0 < w t i := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hn⟩, Finset.mem_univ _⟩
  -- The negative maximum is minus the finite minimum; its zero is attained.
  let g : ℝ → ℝ := fun t => (Finset.univ : Finset (Fin n)).sup' hne (fun i => -w t i)
  have hg : ContinuousOn g (Set.Icc (0 : ℝ) 1) :=
    ContinuousOn.finset_sup'_apply hne
      (fun i _ => ((continuous_apply i).comp_continuousOn hw).neg)
  have hbound : ∀ t i, -w t i ≤ g t := by
    intro t i
    exact Finset.le_sup' (fun j => -w t j) (Finset.mem_univ i)
  have hgzero : g 0 < 0 := by
    obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' hne (fun j => -w 0 j)
    calc
      g 0 = -w 0 i := hi
      _ < 0 := neg_lt_zero.mpr (hzero i)
  intro t ht i
  by_contra hnot
  have hgt : 0 ≤ g t := (neg_nonneg.mpr (le_of_not_gt hnot)).trans (hbound t i)
  have hgsub : ContinuousOn g (Set.Icc (0 : ℝ) t) :=
    hg.mono (fun u hu => ⟨hu.1, hu.2.trans ht.2⟩)
  obtain ⟨u, hu, hgu⟩ := intermediate_value_Icc ht.1 hgsub ⟨hgzero.le, hgt⟩
  have hnonneg : ∀ j, 0 ≤ w u j := by
    intro j
    have hj := hbound u j
    rw [hgu] at hj
    exact neg_nonpos.mp hj
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' hne (fun l => -w u l)
  have heq : g u = -w u j := hj
  have hz : w u j = 0 := neg_eq_zero.mp (heq.symm.trans hgu)
  exact hboundary u ⟨hu.1, hu.2.trans ht.2⟩ hnonneg j hz

end
end NLA.SF01
