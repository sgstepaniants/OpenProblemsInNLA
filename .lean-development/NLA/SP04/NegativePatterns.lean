/-
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. Apache 2.0; AI-assisted.
All eight sign patterns, including the unique maximizing pattern, are explicit.
-/
import NLA.SP04.Normalization

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option leancert.trust "kernel"
open scoped BigOperators
noncomputable section
namespace NLA.SP04

lemma firstNegativePattern_iff (e : Fin 3 → Bool) :
    e = firstNegativePattern ↔ e 0 = true ∧ e 1 = false ∧ e 2 = false := by
  constructor
  · intro h
    subst e
    decide
  · rintro ⟨h0, h1, h2⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

lemma boolean_pattern_maximum (a0 a1 a2 b0 b1 b2 : ℝ)
    (ha0 : 0 < a0) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (hb0 : 0 < b0) (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hba0 : b0 < a0) (hba1 : b1 < a1) (hba2 : b2 < a2)
    (ha01 : a0 < a1) (ha02 : a0 < a2) (hb10 : b1 < b0) (hb20 : b2 < b0)
    (e : Fin 3 → Bool) (he : ∃ i, e i = true) :
    (if e 0 then b0 else a0) * ((if e 1 then b1 else a1) * (if e 2 then b2 else a2))
      ≤ b0 * a1 * a2 ∧
    ((if e 0 then b0 else a0) * ((if e 1 then b1 else a1) * (if e 2 then b2 else a2))
      = b0 * a1 * a2 ↔ e = firstNegativePattern) := by
  have h010 : a0 * b1 * a2 < b0 * a1 * a2 := by
    have h := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos ha01 hb10 ha0 hb0) ha2
    simpa only [mul_comm a1 b0] using h
  have h001 : a0 * a1 * b2 < b0 * a1 * a2 := by
    calc
      a0 * a1 * b2 = (a0 * b2) * a1 := by ring
      _ < (a2 * b0) * a1 :=
        mul_lt_mul_of_pos_right (mul_lt_mul_of_pos ha02 hb20 ha0 hb0) ha1
      _ = b0 * a1 * a2 := by ring
  have h011 : a0 * b1 * b2 < b0 * a1 * a2 :=
    (mul_lt_mul_of_pos_left hba2 (mul_pos ha0 hb1)).trans h010
  have h101 : b0 * a1 * b2 < b0 * a1 * a2 :=
    mul_lt_mul_of_pos_left hba2 (mul_pos hb0 ha1)
  have h110 : b0 * b1 * a2 < b0 * a1 * a2 :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hba1 hb0) ha2
  have h111 : b0 * b1 * b2 < b0 * a1 * a2 :=
    (mul_lt_mul_of_pos_left hba2 (mul_pos hb0 hb1)).trans h110
  rw [firstNegativePattern_iff]
  cases h0 : e 0 <;> cases h1 : e 1 <;> cases h2 : e 2
  · obtain ⟨i, hi⟩ := he
    fin_cases i <;> simp_all
  · simpa [h0, h1, h2, mul_assoc] using And.intro h001.le (ne_of_lt h001)
  · simpa [h0, h1, h2, mul_assoc] using And.intro h010.le (ne_of_lt h010)
  · simpa [h0, h1, h2, mul_assoc] using And.intro h011.le (ne_of_lt h011)
  · simp [h0, h1, h2, mul_assoc]
  · simpa [h0, h1, h2, mul_assoc] using And.intro h101.le (ne_of_lt h101)
  · simpa [h0, h1, h2, mul_assoc] using And.intro h110.le (ne_of_lt h110)
  · simpa [h0, h1, h2, mul_assoc] using And.intro h111.le (ne_of_lt h111)

lemma negative_pattern_abs_product (s : Fin 3 → ℝ) (hs : OrderedBox s)
    (t : ℝ) (ht : 0 < t) (e : Fin 3 → Bool) :
    |∏ i, negativePattern s t e i| =
    (if e 0 then negativeRootMagnitude (s 0) t else positiveNegativeCaseRoot (s 0) t) *
      ((if e 1 then negativeRootMagnitude (s 1) t else positiveNegativeCaseRoot (s 1) t) *
       (if e 2 then negativeRootMagnitude (s 2) t else positiveNegativeCaseRoot (s 2) t)) := by
  have habs (i : Fin 3) : |negativePattern s t e i| =
      if e i then negativeRootMagnitude (s i) t else positiveNegativeCaseRoot (s i) t := by
    have hf := negative_root_facts (s i) (orderedBox_bounds s hs i).1 t ht.le
    unfold negativePattern
    split
    · simp only [abs_neg, abs_of_pos (hf.2.2.2.1 ht)]
    · exact abs_of_pos hf.1
  rw [Finset.abs_prod]
  simp_rw [habs]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]

theorem negative_pattern_dominance (s : Fin 3 → ℝ) (hs : OrderedBox s)
    (t : ℝ) (ht : 0 < t) (e : Fin 3 → Bool) (he : ∃ i, e i = true) :
    |∏ i, negativePattern s t e i| ≤ selectedProduct s t ∧
    (|∏ i, negativePattern s t e i| = selectedProduct s t ↔ e = firstNegativePattern) := by
  have hf (i : Fin 3) := negative_root_facts (s i) (orderedBox_bounds s hs i).1 t ht.le
  have hs01 : s 0 < s 1 := hs.2.1
  have hs02 : s 0 < s 2 := hs.2.1.trans hs.2.2.1
  have ha01 := positive_negative_root_strict_s (orderedBox_pos s hs 0) hs01 ht.le
  have ha02 := positive_negative_root_strict_s (orderedBox_pos s hs 0) hs02 ht.le
  have hb10 := negative_magnitude_strict_s (orderedBox_bounds s hs 0).1 hs01 ht
  have hb20 := negative_magnitude_strict_s (orderedBox_bounds s hs 0).1 hs02 ht
  rw [negative_pattern_abs_product s hs t ht e]
  exact boolean_pattern_maximum
    (positiveNegativeCaseRoot (s 0) t) (positiveNegativeCaseRoot (s 1) t)
    (positiveNegativeCaseRoot (s 2) t) (negativeRootMagnitude (s 0) t)
    (negativeRootMagnitude (s 1) t) (negativeRootMagnitude (s 2) t)
    (hf 0).1 (hf 1).1 (hf 2).1
    ((hf 0).2.2.2.1 ht) ((hf 1).2.2.2.1 ht) ((hf 2).2.2.2.1 ht)
    (hf 0).2.2.1 (hf 1).2.2.1 (hf 2).2.2.1 ha01 ha02 hb10 hb20 e he

#assert_trust kernel negative_pattern_dominance
#print axioms negative_pattern_dominance
end NLA.SP04
