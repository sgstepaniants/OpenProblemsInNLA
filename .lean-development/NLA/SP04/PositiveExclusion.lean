/-
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. Apache 2.0; AI-assisted.
Every positive-root selection is covered by one small-coordinate product bound.
-/
import NLA.SP04.Stationary

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option leancert.trust "kernel"
open scoped BigOperators
noncomputable section
namespace NLA.SP04

lemma positive_triple_product_gt_one (x : Fin 3 → ℝ) (hx : ∀ i, 1 < x i) :
    1 < ∏ i, x i := by
  have h01 := mul_lt_mul_of_pos (hx 0) (hx 1) (by norm_num : (0 : ℝ) < 1)
    (by linarith [hx 1] : 0 < x 1)
  have h012 := mul_lt_mul_of_pos h01 (hx 2) (by norm_num : (0 : ℝ) < 1 * 1)
    (by linarith [hx 2] : 0 < x 2)
  norm_num only [one_mul] at h012
  rw [mul_assoc] at h012
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change (1 : ℝ) < x 0 * (x 1 * x 2)
  exact h012

lemma triple_product_small_coordinate (x : Fin 3 → ℝ) (q b : ℝ)
    (hx : ∀ i, 0 ≤ x i) (hupper : ∀ i, x i ≤ b) (hsmall : ∃ i, x i ≤ q) :
    (∏ i, x i) ≤ q * b ^ 2 := by
  classical
  obtain ⟨i, hi⟩ := hsmall
  have hbound : (∏ j, x j) ≤ ∏ j : Fin 3, if j = i then q else b := by
    apply Finset.prod_le_prod (fun j _ => hx j)
    intro j hj
    by_cases hji : j = i
    · subst j
      rw [if_pos rfl]
      exact hi
    · simpa only [if_neg hji] using hupper j
  have hcap : (∏ j : Fin 3, if j = i then q else b) = q * b ^ 2 := by
    fin_cases i <;> simp [Fin.prod_univ_succ, pow_two, mul_comm, mul_left_comm, mul_assoc]
  exact hcap ▸ hbound

lemma root_selection_product_ne_one (x r q : Fin 3 → ℝ) (a b qcap : ℝ)
    (ha : 1 < a) (hcap : qcap * b ^ 2 < 1)
    (hx : ∀ i, x i = r i ∨ x i = q i)
    (hr : ∀ i, a < r i ∧ r i < b)
    (hq : ∀ i, 0 < q i ∧ q i < r i ∧ q i ≤ qcap) :
    |∏ i, x i| ≠ 1 := by
  have hxpos : ∀ i, 0 < x i := by
    intro i
    rcases hx i with h | h
    · rw [h]
      linarith [(hr i).1]
    · rw [h]
      exact (hq i).1
  have hpnonneg : 0 ≤ ∏ i, x i := Finset.prod_nonneg (fun i _ => (hxpos i).le)
  rw [abs_of_nonneg hpnonneg]
  by_cases hall : ∀ i, x i = r i
  · have hbig : 1 < ∏ i, x i := positive_triple_product_gt_one x (by
      intro i
      rw [hall i]
      exact ha.trans (hr i).1)
    exact ne_of_gt hbig
  · push_neg at hall
    obtain ⟨i, hi⟩ := hall
    have hsmall : x i ≤ qcap := by
      rcases hx i with h | h
      · exact (hi h).elim
      · rw [h]
        exact (hq i).2.2
    have hupper : ∀ j, x j ≤ b := by
      intro j
      rcases hx j with h | h
      · rw [h]
        exact (hr j).2.le
      · rw [h]
        exact ((hq j).2.1.trans (hr j).2).le
    have hbound := triple_product_small_coordinate x qcap b (fun j => (hxpos j).le)
      hupper ⟨i, hsmall⟩
    exact ne_of_lt (hbound.trans_lt hcap)

lemma zero_multiplier_impossible (s x : Fin 3 → ℝ) (hs : OrderedBox s)
    (hroots : ∀ i, x i ^ 2 - s i * x i = 0) (hprod : |∏ i, x i| = 1) : False := by
  have hpne : (∏ i, x i) ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hprod
    norm_num at hprod
  have hxne : ∀ i, x i ≠ 0 := by
    intro i
    exact Finset.prod_ne_zero_iff.mp hpne i (Finset.mem_univ i)
  have heq : ∀ i, x i = s i := by
    intro i
    have hfactor : x i * (x i - s i) = 0 := by nlinarith [hroots i]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left (hxne i))
  have hbig : 1 < ∏ i, x i := positive_triple_product_gt_one x (by
    intro i
    rw [heq i]
    have := (orderedBox_bounds s hs i).1
    linarith)
  rw [abs_of_pos (by linarith : 0 < ∏ i, x i)] at hprod
  linarith

theorem no_small_nonnegative_multiplier (s : Fin 3 → ℝ) (hs : OrderedBox s)
    (X : Mat 3) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 13 / 25) :
    ¬ StationaryPair (Matrix.diagonal s) X c := by
  intro hstationary
  obtain ⟨x, hdiag, hroots, hprod⟩ := stationary_diagonal_reduction s hs X c hstationary
  rcases hc0.eq_or_lt with hz | hcpos
  · have hc : c = 0 := hz.symm
    subst c
    exact zero_multiplier_impossible s x hs (fun i => by simpa using hroots i) hprod
  · have hp (i : Fin 3) := positive_root_certificates (s i) c
      (orderedBox_bounds s hs i).1 (orderedBox_bounds s hs i).2 hcpos hc1
    have hx (i : Fin 3) : x i = positiveLargeRoot (s i) c ∨
        x i = positiveSmallRoot (s i) c := (hp i).2.2.2.2.2.1 (x i) |>.mp (hroots i)
    by_cases hc : c ≤ 2 / 5
    · apply root_selection_product_ne_one x (fun i => positiveLargeRoot (s i) c)
        (fun i => positiveSmallRoot (s i) c) (7 / 5) (44 / 25) (2 / 7)
        (by norm_num) (by norm_num) hx ?_ ?_ hprod
      · intro i
        exact (hp i).2.2.2.2.2.2.1 hc
      · intro i
        have hqpos := (hp i).2.1
        have hlower := ((hp i).2.2.2.2.2.2.1 hc).1
        have hmul := (hp i).2.2.2.1
        refine ⟨hqpos, (hp i).2.2.1, ?_⟩
        nlinarith [mul_pos (sub_pos.mpr hlower) hqpos]
    · have hcgt : 2 / 5 < c := lt_of_not_ge hc
      apply root_selection_product_ne_one x (fun i => positiveLargeRoot (s i) c)
        (fun i => positiveSmallRoot (s i) c) (4 / 3) (3 / 2) (39 / 100)
        (by norm_num) (by norm_num) hx ?_ ?_ hprod
      · intro i
        exact (hp i).2.2.2.2.2.2.2 hcgt
      · intro i
        have hqpos := (hp i).2.1
        have hlower := ((hp i).2.2.2.2.2.2.2 hcgt).1
        have hmul := (hp i).2.2.2.1
        refine ⟨hqpos, (hp i).2.2.1, ?_⟩
        nlinarith [mul_pos (sub_pos.mpr hlower) hqpos]

#assert_trust kernel no_small_nonnegative_multiplier
#print axioms no_small_nonnegative_multiplier
end NLA.SP04
