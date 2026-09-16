/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

The complete LU product equals the specified rational input in its original
row order. The target residual is eliminated by exact rational cancellation.
-/
import NLA.IE13.WitnessFactors
import NLA.IE13.WitnessOrder

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators
namespace NLA.IE13

lemma full_product_early (p q : ℕ) (i j : Fin (witnessOrder p q))
    (hj : j.val < p + q) :
    (∑ r : Fin (witnessOrder p q), fullLowerRational p q i r * fullUpperRational p q r j) =
      witnessScale p * ∑ r : Fin (witnessOrder p q),
        witnessLowerRational p q i r * witnessUpperColumn p q j r := by
  have he (r : Fin (witnessOrder p q)) :
      fullLowerRational p q i r * fullUpperRational p q r j =
        witnessScale p * (witnessLowerRational p q i r * witnessUpperColumn p q j r) := by
    rw [fullUpperRational, if_pos hj]
    by_cases hr : r.val < p + q
    · rw [fullLower_rational_prefix p q i r hr]
      ring
    · rw [upper_column_below p q j r (by change j.val < r.val; omega)]
      ring
  rw [Finset.sum_congr rfl (fun r _ => he r), Finset.mul_sum]

lemma fullUpper_target (p q : ℕ) (r : Fin (witnessOrder p q)) :
    fullUpperRational p q r (witnessTarget p q) =
      if r.val ≤ p + q then forwardRational p r.val else 0 := by
  simp only [fullUpperRational, witnessTarget, Fin.val_mk, lt_self_iff_false,
    if_false, if_pos rfl]

lemma full_product_target_split (p q : ℕ) (i : Fin (witnessOrder p q)) :
    (∑ r : Fin (witnessOrder p q),
      fullLowerRational p q i r * fullUpperRational p q r (witnessTarget p q)) =
      forwardPrefixSum p q i +
        fullLowerRational p q i (witnessTarget p q) * forwardRational p (p + q) := by
  have he (r : Fin (witnessOrder p q)) :
      fullLowerRational p q i r * fullUpperRational p q r (witnessTarget p q) =
        (if r.val < p + q then witnessLowerRational p q i r * forwardRational p r.val else 0) +
        (if r = witnessTarget p q then
          fullLowerRational p q i (witnessTarget p q) * forwardRational p (p + q) else 0) := by
    rw [fullUpper_target]
    by_cases hr : r.val < p + q
    · have hre : r ≠ witnessTarget p q := by
        intro h
        have hv := congrArg Fin.val h
        change r.val = p + q at hv
        omega
      rw [if_pos hr.le, if_pos hr, if_neg hre, fullLower_rational_prefix p q i r hr, add_zero]
    · by_cases hre : r = witnessTarget p q
      · subst r
        simp only [witnessTarget, Fin.val_mk, le_refl, if_true, lt_self_iff_false,
          if_false, if_pos rfl, zero_add]
      · have hrv : r.val ≠ p + q := fun h => hre (Fin.ext h)
        have hrgt : p + q < r.val := by omega
        rw [if_neg (not_le_of_gt hrgt), if_neg hr, if_neg hre, mul_zero, zero_add]
  rw [Finset.sum_congr rfl (fun r _ => he r), Finset.sum_add_distrib]
  simp only [forwardPrefixSum, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma full_product_target (p q : ℕ) (i : Fin (witnessOrder p q)) :
    (∑ r : Fin (witnessOrder p q),
      fullLowerRational p q i r * fullUpperRational p q r (witnessTarget p q)) =
        targetFactorColumn p i.val := by
  by_cases hi : i.val ≤ p + q
  · calc
      (∑ r : Fin (witnessOrder p q),
          fullLowerRational p q i r * fullUpperRational p q r (witnessTarget p q)) =
          ∑ r : Fin (witnessOrder p q), witnessLowerRational p q i r * forwardRational p r.val := by
        apply Finset.sum_congr rfl
        intro r _
        rw [fullLower_rational_initial_row p q i hi r, fullUpper_target]
        by_cases hr : r.val ≤ p + q
        · rw [if_pos hr]
        · have hir : i < r := by change i.val < r.val; omega
          simp only [if_neg hr, lower_rational_above p q i r hir, zero_mul]
      _ = targetFactorColumn p i.val := forward_lower_action p q i
  · rw [full_product_target_split, fullLower_target_below p q i (by omega),
      div_mul_cancel₀ _ (ne_of_gt (forwardRational_pos p (p + q)))]
    ring

lemma full_product_late (p q : ℕ) (i j : Fin (witnessOrder p q)) (hj : p + q < j.val) :
    (∑ r : Fin (witnessOrder p q), fullLowerRational p q i r * fullUpperRational p q r j) =
      if i = j then 1 else 0 := by
  have he : (∑ r : Fin (witnessOrder p q),
      fullLowerRational p q i r * fullUpperRational p q r j) = fullLowerRational p q i j := by
    simp only [fullUpperRational, if_neg (not_lt_of_ge hj.le), if_neg (ne_of_gt hj)]
    simp
  rw [he, fullLower_rational_late p q i j hj]

lemma witnessFactorIndex_late (p q : ℕ) (j : Fin (witnessOrder p q)) (hj : p < j.val) :
    witnessFactorIndex p q j = j := by
  simp only [witnessFactorIndex, dif_neg (not_lt_of_ge hj.le), if_neg (ne_of_gt hj)]

lemma witness_factorization_rational (p q : ℕ) (i j : Fin (witnessOrder p q)) :
    witnessRational p q i j =
      ∑ r : Fin (witnessOrder p q),
        fullLowerRational p q (witnessFactorIndex p q i) r * fullUpperRational p q r j := by
  by_cases hj : j.val < p + q
  · rw [witnessRational, if_pos hj, full_product_early p q _ j hj]
  · rw [witnessRational, if_neg hj]
    by_cases hje : j.val = p + q
    · rw [if_pos hje]
      have hej : j = witnessTarget p q := Fin.ext hje
      rw [hej, full_product_target p q _, targetFactorColumn_original p q i]
    · rw [if_neg hje, full_product_late p q _ j (by omega)]
      have hf : witnessFactorIndex p q j = j := witnessFactorIndex_late p q j (by omega)
      have heq : witnessFactorIndex p q i = j ↔ i = j := by
        constructor
        · intro h
          exact witnessFactorIndex_injective p q (h.trans hf.symm)
        · intro h
          rw [h, hf]
      rw [heq]

lemma witness_factorization (p q : ℕ) (i j : Fin (witnessOrder p q)) :
    witnessMatrix p q i j = (fullLower p q * fullUpper p q) (witnessFactorIndex p q i) j := by
  rw [witnessMatrix, witness_factorization_rational]
  simp only [Matrix.mul_apply, fullLower, fullUpper, Rat.cast_sum, Rat.cast_mul]

#print axioms witness_factorization
#assert_trust kernel witness_factorization

end NLA.IE13
