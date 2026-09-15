/-
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. Apache 2.0; AI-assisted.
Unique minimality is over every real stationary matrix and every real multiplier.
-/
import NLA.SP04.PositiveExclusion
import NLA.SP04.NegativePatterns
import NLA.SP04.Frobenius

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option leancert.trust "kernel"
open scoped BigOperators
noncomputable section
namespace NLA.SP04

lemma selected_pattern_product (s : Fin 3 → ℝ) (t : ℝ) :
    (∏ i, negativePattern s t firstNegativePattern i) = -selectedProduct s t := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change (-negativeRootMagnitude (s 0) t) *
      (positiveNegativeCaseRoot (s 1) t * positiveNegativeCaseRoot (s 2) t) =
    -(negativeRootMagnitude (s 0) t * positiveNegativeCaseRoot (s 1) t *
      positiveNegativeCaseRoot (s 2) t)
  ring

lemma negative_pattern_stationary (s : Fin 3 → ℝ) (hs : OrderedBox s)
    (t : ℝ) (ht : 0 ≤ t) (e : Fin 3 → Bool)
    (hprod : |∏ i, negativePattern s t e i| = 1) :
    StationaryPair (Matrix.diagonal s) (Matrix.diagonal (negativePattern s t e)) (-t) := by
  apply diagonal_stationary_of_roots s (negativePattern s t e) (-t) hprod
  intro i
  have hf := negative_root_facts (s i) (orderedBox_bounds s hs i).1 t ht
  have hchoice : negativePattern s t e i = positiveNegativeCaseRoot (s i) t ∨
      negativePattern s t e i = -negativeRootMagnitude (s i) t := by
    unfold negativePattern
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hquad := (hf.2.2.2.2.2.2 _).mpr hchoice
  simpa only [sub_eq_add_neg] using hquad

lemma every_negative_stationary_pattern (s : Fin 3 → ℝ) (hs : OrderedBox s)
    (Y : Mat 3) (t : ℝ) (ht : 0 < t)
    (hY : StationaryPair (Matrix.diagonal s) Y (-t)) :
    ∃ e : Fin 3 → Bool, (∃ i, e i = true) ∧
      Y = Matrix.diagonal (negativePattern s t e) ∧
      |∏ i, negativePattern s t e i| = 1 := by
  classical
  obtain ⟨x, hdiag, hroots, hprod⟩ := stationary_diagonal_reduction s hs Y (-t) hY
  have hf (i : Fin 3) := negative_root_facts (s i) (orderedBox_bounds s hs i).1 t ht.le
  have hchoices : ∀ i : Fin 3, ∃ b : Bool,
      x i = if b then -negativeRootMagnitude (s i) t else positiveNegativeCaseRoot (s i) t := by
    intro i
    have hquad : x i ^ 2 - s i * x i - t = 0 := by simpa only [sub_eq_add_neg] using hroots i
    rcases ((hf i).2.2.2.2.2.2 (x i)).mp hquad with hp | hn
    · exact ⟨false, hp⟩
    · exact ⟨true, hn⟩
  choose e he using hchoices
  have hxeq : x = negativePattern s t e := funext he
  have hneg : ∃ i, e i = true := by
    by_contra hnone
    have hefalse : ∀ i, e i = false := by
      intro i
      cases hi : e i
      · rfl
      · exact (hnone ⟨i, hi⟩).elim
    have hbig : 1 < ∏ i, x i := positive_triple_product_gt_one x (by
      intro i
      have hxi : x i = positiveNegativeCaseRoot (s i) t := by
        simpa only [hefalse i, Bool.false_eq_true, ↓reduceIte] using he i
      rw [hxi]
      have hbnonneg := (hf i).2.1
      have hdiff := (hf i).2.2.2.2.2.1
      have hsi := (orderedBox_bounds s hs i).1
      linarith)
    rw [abs_of_pos (by linarith : 0 < ∏ i, x i)] at hprod
    linarith
  refine ⟨e, hneg, ?_, ?_⟩
  · exact hdiag.trans (congrArg Matrix.diagonal hxeq)
  · rw [← hxeq]
    exact hprod

lemma stationary_with_bounded_multiplier_is_selected (s : Fin 3 → ℝ) (hs : OrderedBox s)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 13 / 25) (hg : selectedProduct s t = 1)
    (Y : Mat 3) (d : ℝ) (hY : StationaryPair (Matrix.diagonal s) Y d)
    (hd : |d| ≤ t) : Y = selectedMatrix s t ∧ d = -t := by
  by_cases hd0 : 0 ≤ d
  · have hd1 : d ≤ 13 / 25 := (le_abs_self d).trans (hd.trans ht1.le)
    exact (no_small_nonnegative_multiplier s hs Y d hd0 hd1 hY).elim
  · have hdneg : d < 0 := lt_of_not_ge hd0
    have hu0 : 0 < -d := neg_pos.mpr hdneg
    have hut : -d ≤ t := by simpa only [abs_of_neg hdneg] using hd
    have hYneg : StationaryPair (Matrix.diagonal s) Y (-(-d)) := by simpa only [neg_neg] using hY
    obtain ⟨e, he, hdiag, hprod⟩ := every_negative_stationary_pattern s hs Y (-d) hu0 hYneg
    have hdom := negative_pattern_dominance s hs (-d) hu0 e he
    have hgle : 1 ≤ selectedProduct s (-d) := hprod ▸ hdom.1
    have htu : -d = t := by
      apply le_antisymm hut
      by_contra h
      have hlt : -d < t := lt_of_not_ge h
      have hmono := selected_product_strictMono s hs hu0.le ht0.le hlt
      rw [hg] at hmono
      exact (not_lt_of_ge hgle hmono)
    have hgu : selectedProduct s (-d) = 1 := by rw [htu, hg]
    have hefirst : e = firstNegativePattern := hdom.2.mp (hprod.trans hgu.symm)
    constructor
    · rw [hdiag, hefirst, htu]
      rfl
    · linarith

lemma selected_unique_least (s : Fin 3 → ℝ) (hs : OrderedBox s)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 13 / 25) (hg : selectedProduct s t = 1) :
    UniqueLeastAbsoluteMultiplier (Matrix.diagonal s) (selectedMatrix s t) (-t) := by
  have hprod : |∏ i, negativePattern s t firstNegativePattern i| = 1 := by
    rw [selected_pattern_product, hg]
    norm_num
  have hstationary : StationaryPair (Matrix.diagonal s) (selectedMatrix s t) (-t) :=
    negative_pattern_stationary s hs t ht0.le firstNegativePattern hprod
  refine ⟨⟨hstationary, ?_⟩, ?_⟩
  · intro Y d hY
    rw [abs_neg, abs_of_pos ht0]
    by_cases hd : t ≤ |d|
    · exact hd
    · have hsmall : |d| ≤ t := (lt_of_not_ge hd).le
      have heq := stationary_with_bounded_multiplier_is_selected s hs t ht0 ht1 hg Y d hY hsmall
      rw [heq.2, abs_neg, abs_of_pos ht0] at hd
      exact (hd le_rfl).elim
  · intro Y d hY hd
    apply stationary_with_bounded_multiplier_is_selected s hs t ht0 ht1 hg Y d hY
    simpa only [abs_neg, abs_of_pos ht0] using hd

lemma improving_matrix_feasible (s : Fin 3 → ℝ) (t : ℝ) (hg : selectedProduct s t = 1) :
    UnitAbsoluteDeterminant (improvingMatrix s t) := by
  unfold UnitAbsoluteDeterminant improvingMatrix
  rw [Matrix.det_diagonal]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change |negativeRootMagnitude (s 0) t *
    (positiveNegativeCaseRoot (s 1) t * positiveNegativeCaseRoot (s 2) t)| = 1
  rw [← mul_assoc]
  change |selectedProduct s t| = 1
  rw [hg]
  norm_num

lemma diagonal_distance_improvement (s : Fin 3 → ℝ) (t : ℝ) :
    frobeniusDistance (Matrix.diagonal s) (selectedMatrix s t) ^ 2 -
      frobeniusDistance (Matrix.diagonal s) (improvingMatrix s t) ^ 2 =
      4 * s 0 * negativeRootMagnitude (s 0) t := by
  unfold selectedMatrix improvingMatrix
  rw [frobenius_diagonal_distance_sq, frobenius_diagonal_distance_sq]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (s 0 - -negativeRootMagnitude (s 0) t) ^ 2 +
      ((s 1 - positiveNegativeCaseRoot (s 1) t) ^ 2 +
       (s 2 - positiveNegativeCaseRoot (s 2) t) ^ 2) -
    ((s 0 - negativeRootMagnitude (s 0) t) ^ 2 +
      ((s 1 - positiveNegativeCaseRoot (s 1) t) ^ 2 +
       (s 2 - positiveNegativeCaseRoot (s 2) t) ^ 2)) =
    4 * s 0 * negativeRootMagnitude (s 0) t
  ring

theorem diagonal_unique_counterexample (s : Fin 3 → ℝ) (hs : OrderedBox s) :
    ∃ t : ℝ, 0 < t ∧ t < 13 / 25 ∧ selectedProduct s t = 1 ∧
      UniqueLeastAbsoluteMultiplier (Matrix.diagonal s) (selectedMatrix s t) (-t) ∧
      UnitAbsoluteDeterminant (improvingMatrix s t) ∧
      frobeniusDistance (Matrix.diagonal s) (selectedMatrix s t) ^ 2 -
        frobeniusDistance (Matrix.diagonal s) (improvingMatrix s t) ^ 2 =
        4 * s 0 * negativeRootMagnitude (s 0) t ∧
      frobeniusDistance (Matrix.diagonal s) (improvingMatrix s t) <
        frobeniusDistance (Matrix.diagonal s) (selectedMatrix s t) := by
  obtain ⟨t, ⟨ht0, ht1, hg⟩, huniq⟩ := (selected_product_normalization s hs).2.2.2.2
  have himp := diagonal_distance_improvement s t
  refine ⟨t, ht0, ht1, hg, selected_unique_least s hs t ht0 ht1 hg,
    improving_matrix_feasible s t hg, himp, ?_⟩
  have hb0 := (negative_root_facts (s 0) (orderedBox_bounds s hs 0).1 t ht0.le).2.2.2.1 ht0
  have hpos : 0 < 4 * s 0 * negativeRootMagnitude (s 0) t :=
    mul_pos (mul_pos (by norm_num) (orderedBox_pos s hs 0)) hb0
  have hselected := (frobenius_norm_squared (Matrix.diagonal s - selectedMatrix s t)).1
  have himproving := (frobenius_norm_squared (Matrix.diagonal s - improvingMatrix s t)).1
  change 0 ≤ frobeniusDistance (Matrix.diagonal s) (selectedMatrix s t) at hselected
  change 0 ≤ frobeniusDistance (Matrix.diagonal s) (improvingMatrix s t) at himproving
  exact (sq_lt_sq₀ himproving hselected).mp (by linarith)

#assert_trust kernel diagonal_unique_counterexample
#print axioms diagonal_unique_counterexample
end NLA.SP04
