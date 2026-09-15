/-
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. Apache 2.0; AI-assisted.
All root bounds reduce to exact quadratic inequalities. No interval subdivision.
-/
import NLA.SP04.Definitions
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option leancert.trust "kernel"
open scoped BigOperators
noncomputable section
namespace NLA.SP04

lemma orderedBox_bounds (s : Fin 3 → ℝ) (hs : OrderedBox s) (i : Fin 3) :
    7 / 4 < s i ∧ s i < 44 / 25 := by
  rcases hs with ⟨h0, h1, h2, h3⟩
  fin_cases i
  · change 7 / 4 < s 0 ∧ s 0 < 44 / 25
    constructor <;> linarith
  · change 7 / 4 < s 1 ∧ s 1 < 44 / 25
    constructor <;> linarith
  · change 7 / 4 < s 2 ∧ s 2 < 44 / 25
    constructor <;> linarith

lemma orderedBox_pos (s : Fin 3 → ℝ) (hs : OrderedBox s) (i : Fin 3) :
    0 < s i := by
  have := (orderedBox_bounds s hs i).1
  linarith

theorem positive_root_certificates (s c : ℝ)
    (hs0 : 7 / 4 < s) (hs1 : s < 44 / 25) (hc0 : 0 < c) (hc1 : c ≤ 13 / 25) :
    0 < s ^ 2 - 4 * c ∧
    0 < positiveSmallRoot s c ∧ positiveSmallRoot s c < positiveLargeRoot s c ∧
    positiveLargeRoot s c * positiveSmallRoot s c = c ∧
    positiveLargeRoot s c + positiveSmallRoot s c = s ∧
    (∀ x : ℝ, x ^ 2 - s * x + c = 0 ↔
      x = positiveLargeRoot s c ∨ x = positiveSmallRoot s c) ∧
    (c ≤ 2 / 5 → 7 / 5 < positiveLargeRoot s c ∧ positiveLargeRoot s c < 44 / 25) ∧
    (2 / 5 < c → 4 / 3 < positiveLargeRoot s c ∧ positiveLargeRoot s c < 3 / 2) := by
  have hs : 0 < s := by linarith
  have hD : 0 < s ^ 2 - 4 * c := by nlinarith [sq_nonneg (s - 7 / 4)]
  have hroot : 0 < Real.sqrt (s ^ 2 - 4 * c) := Real.sqrt_pos.2 hD
  have hroot_sq := Real.sq_sqrt hD.le
  have hroot_lt : Real.sqrt (s ^ 2 - 4 * c) < s :=
    (Real.sqrt_lt' hs).2 (by linarith)
  have hprod : positiveLargeRoot s c * positiveSmallRoot s c = c := by
    dsimp [positiveLargeRoot, positiveSmallRoot]
    nlinarith
  have hsum : positiveLargeRoot s c + positiveSmallRoot s c = s := by
    dsimp [positiveLargeRoot, positiveSmallRoot]
    ring
  refine ⟨hD, ?_, ?_, hprod, hsum, ?_, ?_, ?_⟩
  · dsimp [positiveSmallRoot]
    linarith
  · dsimp [positiveSmallRoot, positiveLargeRoot]
    linarith
  · intro x
    have hfactor : x ^ 2 - s * x + c =
        (x - positiveLargeRoot s c) * (x - positiveSmallRoot s c) := by
      linear_combination x * hsum - hprod
    rw [hfactor, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  · intro hc
    have htest : (14 / 5 - s) ^ 2 < s ^ 2 - 4 * c := by nlinarith
    have hlow := Real.lt_sqrt_of_sq_lt htest
    dsimp [positiveLargeRoot]
    constructor <;> linarith
  · intro hc
    have htest : (8 / 3 - s) ^ 2 < s ^ 2 - 4 * c := by nlinarith
    have hlow := Real.lt_sqrt_of_sq_lt htest
    have hhigh : Real.sqrt (s ^ 2 - 4 * c) < 3 - s :=
      (Real.sqrt_lt' (by linarith)).2 (by nlinarith)
    dsimp [positiveLargeRoot]
    constructor <;> linarith

lemma negative_root_continuous (s : ℝ) :
    Continuous (positiveNegativeCaseRoot s) ∧ Continuous (negativeRootMagnitude s) := by
  constructor
  · unfold positiveNegativeCaseRoot
    fun_prop
  · unfold negativeRootMagnitude
    fun_prop

lemma negative_roots_strictMono (s : ℝ) :
    StrictMonoOn (positiveNegativeCaseRoot s) (Set.Ici 0) ∧
    StrictMonoOn (negativeRootMagnitude s) (Set.Ici 0) := by
  constructor
  · intro t ht u hu htu
    have ht0 : 0 ≤ t := ht
    have hrad : 0 ≤ s ^ 2 + 4 * t := by nlinarith [sq_nonneg s]
    have hr := Real.sqrt_lt_sqrt hrad (show s ^ 2 + 4 * t < s ^ 2 + 4 * u by linarith)
    dsimp [positiveNegativeCaseRoot]
    linarith
  · intro t ht u hu htu
    have ht0 : 0 ≤ t := ht
    have hrad : 0 ≤ s ^ 2 + 4 * t := by nlinarith [sq_nonneg s]
    have hr := Real.sqrt_lt_sqrt hrad (show s ^ 2 + 4 * t < s ^ 2 + 4 * u by linarith)
    dsimp [negativeRootMagnitude]
    linarith

theorem negative_root_certificates (s : ℝ) (hs : 7 / 4 < s) :
    ContinuousOn (positiveNegativeCaseRoot s) (Set.Ici 0) ∧
    ContinuousOn (negativeRootMagnitude s) (Set.Ici 0) ∧
    StrictMonoOn (positiveNegativeCaseRoot s) (Set.Ici 0) ∧
    StrictMonoOn (negativeRootMagnitude s) (Set.Ici 0) ∧
    ∀ t : ℝ, 0 ≤ t →
      0 < positiveNegativeCaseRoot s t ∧ 0 ≤ negativeRootMagnitude s t ∧
      negativeRootMagnitude s t < positiveNegativeCaseRoot s t ∧
      (0 < t → 0 < negativeRootMagnitude s t) ∧
      positiveNegativeCaseRoot s t * negativeRootMagnitude s t = t ∧
      positiveNegativeCaseRoot s t - negativeRootMagnitude s t = s ∧
      (∀ x : ℝ, x ^ 2 - s * x - t = 0 ↔
        x = positiveNegativeCaseRoot s t ∨ x = -negativeRootMagnitude s t) := by
  refine ⟨(negative_root_continuous s).1.continuousOn,
    (negative_root_continuous s).2.continuousOn,
    (negative_roots_strictMono s).1, (negative_roots_strictMono s).2, ?_⟩
  intro t ht
  have hspos : 0 < s := by linarith
  have hrad : 0 ≤ s ^ 2 + 4 * t := by nlinarith [sq_nonneg s]
  have hroot_sq := Real.sq_sqrt hrad
  have hroot_nonneg := Real.sqrt_nonneg (s ^ 2 + 4 * t)
  have hroot_ge : s ≤ Real.sqrt (s ^ 2 + 4 * t) := by nlinarith
  have hprod : positiveNegativeCaseRoot s t * negativeRootMagnitude s t = t := by
    dsimp [positiveNegativeCaseRoot, negativeRootMagnitude]
    nlinarith
  have hsub : positiveNegativeCaseRoot s t - negativeRootMagnitude s t = s := by
    dsimp [positiveNegativeCaseRoot, negativeRootMagnitude]
    ring
  refine ⟨?_, ?_, ?_, ?_, hprod, hsub, ?_⟩
  · dsimp [positiveNegativeCaseRoot]
    linarith
  · dsimp [negativeRootMagnitude]
    linarith
  · linarith
  · intro htpos
    have hstrict : s < Real.sqrt (s ^ 2 + 4 * t) :=
      Real.lt_sqrt_of_sq_lt (by linarith)
    dsimp [negativeRootMagnitude]
    linarith
  · intro x
    have hfactor : x ^ 2 - s * x - t =
        (x - positiveNegativeCaseRoot s t) * (x + negativeRootMagnitude s t) := by
      linear_combination x * hsub + hprod
    rw [hfactor, mul_eq_zero, sub_eq_zero, add_eq_zero_iff_eq_neg]

#assert_trust kernel positive_root_certificates
#print axioms positive_root_certificates
#assert_trust kernel negative_root_certificates
#print axioms negative_root_certificates
end NLA.SP04
