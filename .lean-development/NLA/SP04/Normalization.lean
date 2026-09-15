/-
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. Apache 2.0; AI-assisted.
The unique parameter follows from exact endpoint bounds and the ordinary IVT.
-/
import NLA.SP04.ScalarRoots

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option leancert.trust "kernel"
open scoped BigOperators
noncomputable section
namespace NLA.SP04

lemma negative_root_facts (s : ℝ) (hs : 7 / 4 < s) (t : ℝ) (ht : 0 ≤ t) :
    0 < positiveNegativeCaseRoot s t ∧ 0 ≤ negativeRootMagnitude s t ∧
    negativeRootMagnitude s t < positiveNegativeCaseRoot s t ∧
    (0 < t → 0 < negativeRootMagnitude s t) ∧
    positiveNegativeCaseRoot s t * negativeRootMagnitude s t = t ∧
    positiveNegativeCaseRoot s t - negativeRootMagnitude s t = s ∧
    (∀ x : ℝ, x ^ 2 - s * x - t = 0 ↔
      x = positiveNegativeCaseRoot s t ∨ x = -negativeRootMagnitude s t) :=
  (negative_root_certificates s hs).2.2.2.2 t ht

lemma negative_root_zero (s : ℝ) (hs : 0 < s) :
    positiveNegativeCaseRoot s 0 = s ∧ negativeRootMagnitude s 0 = 0 := by
  simp [positiveNegativeCaseRoot, negativeRootMagnitude,
    Real.sqrt_sq_eq_abs, abs_of_pos hs]

lemma negative_root_endpoint (s : ℝ) (hs0 : 7 / 4 < s) (hs1 : s < 44 / 25) :
    2 < positiveNegativeCaseRoot s (13 / 25) ∧
    1 / 4 < negativeRootMagnitude s (13 / 25) := by
  have ha : 4 - s < Real.sqrt (s ^ 2 + 4 * (13 / 25)) :=
    Real.lt_sqrt_of_sq_lt (by nlinarith)
  have hb : s + 1 / 2 < Real.sqrt (s ^ 2 + 4 * (13 / 25)) :=
    Real.lt_sqrt_of_sq_lt (by nlinarith)
  dsimp [positiveNegativeCaseRoot, negativeRootMagnitude]
  constructor <;> linarith

lemma selected_product_continuous (s : Fin 3 → ℝ) :
    Continuous (selectedProduct s) := by
  exact ((negative_root_continuous (s 0)).2.mul
    (negative_root_continuous (s 1)).1).mul
      (negative_root_continuous (s 2)).1

lemma selected_product_strictMono (s : Fin 3 → ℝ) (hs : OrderedBox s) :
    StrictMonoOn (selectedProduct s) (Set.Ici 0) := by
  intro t ht u hu htu
  have ht0 : 0 ≤ t := ht
  have hu0 : 0 ≤ u := hu
  have hb := (negative_roots_strictMono (s 0)).2 ht hu htu
  have ha1 := (negative_roots_strictMono (s 1)).1 ht hu htu
  have ha2 := (negative_roots_strictMono (s 2)).1 ht hu htu
  have hbun := (negative_root_facts (s 0) (orderedBox_bounds s hs 0).1 u hu0).2.1
  have ha1tp := (negative_root_facts (s 1) (orderedBox_bounds s hs 1).1 t ht0).1
  have ha1up := (negative_root_facts (s 1) (orderedBox_bounds s hs 1).1 u hu0).1
  have ha2tp := (negative_root_facts (s 2) (orderedBox_bounds s hs 2).1 t ht0).1
  have hfirst := mul_lt_mul_of_lt_of_le_of_pos_of_nonneg hb ha1.le ha1tp hbun
  exact mul_lt_mul_of_lt_of_le_of_pos_of_nonneg hfirst ha2.le ha2tp
    (mul_nonneg hbun ha1up.le)

lemma selected_product_zero (s : Fin 3 → ℝ) (hs : OrderedBox s) :
    selectedProduct s 0 = 0 := by
  unfold selectedProduct
  rw [(negative_root_zero (s 0) (orderedBox_pos s hs 0)).2]
  simp

lemma selected_product_endpoint (s : Fin 3 → ℝ) (hs : OrderedBox s) :
    1 < selectedProduct s (13 / 25) := by
  have h0 := (negative_root_endpoint (s 0) (orderedBox_bounds s hs 0).1
    (orderedBox_bounds s hs 0).2).2
  have h1 := (negative_root_endpoint (s 1) (orderedBox_bounds s hs 1).1
    (orderedBox_bounds s hs 1).2).1
  have h2 := (negative_root_endpoint (s 2) (orderedBox_bounds s hs 2).1
    (orderedBox_bounds s hs 2).2).1
  have hfirst : (1 / 4 : ℝ) * 2 < negativeRootMagnitude (s 0) (13 / 25) *
      positiveNegativeCaseRoot (s 1) (13 / 25) :=
    mul_lt_mul_of_pos h0 h1 (by norm_num) (by linarith)
  have hfull := mul_lt_mul_of_pos hfirst h2 (by norm_num : (0 : ℝ) < (1 / 4) * 2)
    (by linarith : 0 < positiveNegativeCaseRoot (s 2) (13 / 25))
  norm_num [selectedProduct] at hfull ⊢
  exact hfull

theorem selected_product_normalization (s : Fin 3 → ℝ) (hs : OrderedBox s) :
    ContinuousOn (selectedProduct s) (Set.Icc 0 (13 / 25)) ∧
    StrictMonoOn (selectedProduct s) (Set.Ici 0) ∧
    selectedProduct s 0 = 0 ∧ 1 < selectedProduct s (13 / 25) ∧
    ∃! t : ℝ, 0 < t ∧ t < 13 / 25 ∧ selectedProduct s t = 1 := by
  have hc := (selected_product_continuous s).continuousOn
  have hm := selected_product_strictMono s hs
  have hz := selected_product_zero s hs
  have he := selected_product_endpoint s hs
  refine ⟨hc, hm, hz, he, ?_⟩
  have hmiddle : (1 : ℝ) ∈ Set.Icc (selectedProduct s 0)
      (selectedProduct s (13 / 25)) := by
    rw [hz]
    exact ⟨by norm_num, he.le⟩
  obtain ⟨t, ht, hvalue⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 13 / 25)
    hc hmiddle
  have htpos : 0 < t := by
    by_contra h
    have htzero : t = 0 := le_antisymm (le_of_not_gt h) ht.1
    rw [htzero, hz] at hvalue
    norm_num at hvalue
  have htend : t < 13 / 25 := by
    by_contra h
    have hteq : t = 13 / 25 := le_antisymm ht.2 (le_of_not_gt h)
    rw [hteq] at hvalue
    linarith
  refine ⟨t, ⟨htpos, htend, hvalue⟩, ?_⟩
  intro u hu
  exact hm.injOn hu.1.le htpos.le (hu.2.2.trans hvalue.symm)

lemma positive_negative_root_strict_s {s r t : ℝ}
    (hs : 0 < s) (hsr : s < r) (ht : 0 ≤ t) :
    positiveNegativeCaseRoot s t < positiveNegativeCaseRoot r t := by
  have hrad : 0 ≤ s ^ 2 + 4 * t := by nlinarith [sq_nonneg s]
  have hradlt : s ^ 2 + 4 * t < r ^ 2 + 4 * t := by nlinarith
  have hroot := Real.sqrt_lt_sqrt hrad hradlt
  dsimp [positiveNegativeCaseRoot]
  linarith

lemma negative_magnitude_strict_s {s r t : ℝ}
    (hs : 7 / 4 < s) (hsr : s < r) (ht : 0 < t) :
    negativeRootMagnitude r t < negativeRootMagnitude s t := by
  have hs0 : 0 < s := by linarith
  have hr : 7 / 4 < r := hs.trans hsr
  have hsf := negative_root_facts s hs t ht.le
  have hrf := negative_root_facts r hr t ht.le
  have ha := positive_negative_root_strict_s hs0 hsr ht.le
  have hsb : 0 < negativeRootMagnitude s t := hsf.2.2.2.1 ht
  have hrb : 0 < negativeRootMagnitude r t := hrf.2.2.2.1 ht
  have hsp := hsf.2.2.2.2.1
  have hrp := hrf.2.2.2.2.1
  nlinarith [mul_pos (sub_pos.mpr ha) hrb]

#assert_trust kernel selected_product_normalization
#print axioms selected_product_normalization
end NLA.SP04
