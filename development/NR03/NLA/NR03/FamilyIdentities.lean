/-
NR-03 modular bounded development draft.

This file is a mechanically separated portion of the source candidate at
commit d8b65ab13ee9c27e8909052de792f10322a51e1b. It preserves the approved
Definitions/Challenge boundary. This scratch package is not a verification
claim; authoritative LeanCert, Comparator, kernel and sandbox checks remain
pending.
-/
import NLA.NR03.Core
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
open scoped BigOperators Matrix
noncomputable section

namespace NLA.NR03

/- Each remaining source family is explicitly finite.  The singleton, pair,
   and four-set identities inspect only 7, 21, or 35 summands per row-local
   check; the closed-family identity below is reduced further to its two
   cardinality parameters.  The large 128-by-127 matrix multiplication is
   never unfolded. -/
theorem singleton_identity : ∀ a b : Mask7,
    singletonSum a b = singletonClosed a b := by
  decide +kernel

theorem pair_identity : ∀ a b : Mask7,
    pairSum a b = pairClosed a b := by
  decide +kernel

theorem four_identity : ∀ a b : Mask7,
    fourSum a b = fourClosed a b := by
  decide +kernel

theorem natBool_le_one (b : Bool) : natBool b ≤ 1 := by
  cases b <;> simp [natBool]

theorem maskCard_le_seven (b : Mask7) : maskCard b ≤ 7 := by
  unfold maskCard
  calc
    (∑ i : Fin 7, natBool (maskVector b i)) ≤ ∑ i : Fin 7, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact natBool_le_one _
    _ = 7 := by simp

theorem maskDot_le_card (a b : Mask7) :
    maskDot a b ≤ maskCard b := by
  unfold maskDot maskCard
  apply Finset.sum_le_sum
  intro i hi
  cases ha : maskVector a i <;> cases hb : maskVector b i <;>
    simp [natBool, ha, hb]

/- The closed family calculation depends only on the two cardinality
   parameters s = |b| and t = |a ∩ b|.  It is checked over Fin 8 squared
   (with the implication t ≤ s), rather than by expanding all 128^2 mask
   pairs. -/
theorem closed_arithmetic :
    ∀ s t : Fin 8, t.val ≤ s.val →
      natSquareOneMinus t.val * natSquareOneMinus (s.val - t.val) +
          (if s.val = 1 then 1 - t.val else 0) +
          4 * (s.val - 2) * Nat.choose t.val 2 +
          12 * ((s.val - t.val) * Nat.choose t.val 3 +
            2 * Nat.choose t.val 4) =
        (if s.val ≤ 1 then 1 else (s.val - 1) ^ 2) *
          natSquareOneMinus t.val := by
  decide +kernel

theorem closed_family_identity : ∀ a b : Mask7,
    coreClosed a b + singletonClosed a b + pairClosed a b + fourClosed a b =
      sourceD b * natTarget a b := by
  intro a b
  have hs : maskCard b ≤ 7 := maskCard_le_seven b
  have ht : maskDot a b ≤ maskCard b := maskDot_le_card a b
  let s : Fin 8 := ⟨maskCard b, by omega⟩
  let t : Fin 8 := ⟨maskDot a b, by omega⟩
  have hst : t.val ≤ s.val := by
    simpa [s, t] using ht
  have h := closed_arithmetic s t hst
  simpa [coreClosed, singletonClosed, pairClosed, fourClosed,
    sourceD, natTarget, s, t] using h

end NLA.NR03
