/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

The prescribed repeated physical swaps perform the exact original-label
rotation. There is no preliminary row permutation in the algorithm.
-/
import NLA.IE13.Origin

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.IE13

lemma witness_seed_positions (p q : ℕ) : PositionsValid (witnessSeedPath p q) := by
  intro k
  unfold witnessSeedPath
  split_ifs with hk
  · exact hk
  · exact le_rfl

lemma witness_seed_ge (p q : ℕ) (k : Fin (witnessOrder p q)) (hk : p ≤ k.val) :
    witnessSeedPath p q k = k := by
  unfold witnessSeedPath
  split_ifs with h
  · apply Fin.ext
    simp only [Fin.val_mk]
    omega
  · rfl

lemma origin_seed_small (p q k : ℕ) :
    ∀ hk : k ≤ p, ∀ i : Fin (witnessOrder p q),
      (origin (witnessSeedPath p q) k i).val =
        if i.val < k then (if i.val = 0 then p else i.val - 1)
        else if i.val = p then (if k = 0 then p else k - 1) else i.val := by
  induction k with
  | zero =>
    intro hk i
    simp only [origin, Equiv.refl_apply, Nat.not_lt_zero, if_false, if_pos rfl] <;>
      split_ifs <;> omega
  | succ k ih =>
    intro hk i
    have hkp : k < p := by omega
    have hkn : k < witnessOrder p q := by unfold witnessOrder; omega
    let z : Fin (witnessOrder p q) := ⟨k, hkn⟩
    let f : Fin (witnessOrder p q) := ⟨p, by unfold witnessOrder; omega⟩
    have hseed : witnessSeedPath p q z = f := by
      simp only [witnessSeedPath, z, if_pos hkp.le] <;> rfl
    rw [origin_step (witnessSeedPath p q) k hkn]
    change (origin (witnessSeedPath p q) k (Equiv.swap z (witnessSeedPath p q z) i)).val = _
    rw [hseed]
    by_cases hiz : i = z
    · subst i
      rw [Equiv.swap_apply_left, ih hkp.le f]
      simp only [z, f, Fin.val_mk]
      split_ifs <;> omega
    · by_cases hif : i = f
      · subst i
        rw [Equiv.swap_apply_right, ih hkp.le z]
        have hpk : ¬p < k + 1 := by omega
        simp [z, f, hpk, ne_of_lt hkp]
      · rw [Equiv.swap_apply_of_ne_of_ne hiz hif, ih hkp.le i]
        have hizv : i.val ≠ k := fun h => hiz (Fin.ext h)
        have hifv : i.val ≠ p := fun h => hif (Fin.ext h)
        split_ifs <;> omega

lemma origin_seed_stable (p q k : ℕ) (hk : p ≤ k) :
    origin (witnessSeedPath p q) (k + 1) = origin (witnessSeedPath p q) k := by
  by_cases hkn : k < witnessOrder p q
  · rw [origin, dif_pos hkn, witness_seed_ge p q ⟨k, hkn⟩ hk]
    simp only [Equiv.swap_self, Equiv.refl_trans]
  · rw [origin, dif_neg hkn]

lemma origin_seed_after (p q s : ℕ) :
    origin (witnessSeedPath p q) (p + s) = origin (witnessSeedPath p q) p := by
  induction s with
  | zero => rw [Nat.add_zero]
  | succ s ih =>
    rw [show p + (s + 1) = (p + s) + 1 by omega,
      origin_seed_stable p q (p + s) (by omega), ih]

theorem witness_prefix_order (p q : ℕ) :
    PositionsValid (witnessSeedPath p q) ∧
    ∀ i : Fin (witnessOrder p q),
      (origin (witnessSeedPath p q) (p + q) i).val =
        if i.val = 0 then p else if i.val ≤ p then i.val - 1 else i.val := by
  refine ⟨witness_seed_positions p q, ?_⟩
  intro i
  rw [origin_seed_after p q q, origin_seed_small p q p le_rfl i]
  split_ifs <;> omega

lemma witnessFactorIndex_injective (p q : ℕ) :
    Function.Injective (witnessFactorIndex p q) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp only [witnessFactorIndex] at hv
  split_ifs at hv <;> (try simp only [Fin.val_mk] at hv) <;> omega

def witnessFactorEquiv (p q : ℕ) : Equiv.Perm (Fin (witnessOrder p q)) :=
  Equiv.ofBijective (witnessFactorIndex p q) ⟨witnessFactorIndex_injective p q,
    Finite.surjective_of_injective (witnessFactorIndex_injective p q)⟩

lemma witness_factor_origin_small (p q k : ℕ) (hk : k ≤ p)
    (i : Fin (witnessOrder p q)) :
    (witnessFactorIndex p q (origin (witnessSeedPath p q) k i)).val =
      if i.val < k then i.val else if i.val = p then k
      else if i.val < p then i.val + 1 else i.val := by
  have ho := origin_seed_small p q k hk i
  unfold witnessFactorIndex
  split_ifs <;> (try simp only [Fin.val_mk])
  all_goals split_ifs at ho ⊢ <;> omega

lemma witness_factor_origin_after (p q s : ℕ) (i : Fin (witnessOrder p q)) :
    witnessFactorIndex p q (origin (witnessSeedPath p q) (p + s) i) = i := by
  apply Fin.ext
  rw [origin_seed_after p q s, witness_factor_origin_small p q p le_rfl i]
  split_ifs <;> omega

lemma witness_factor_origin_ge (p q k : ℕ) (hk : p ≤ k)
    (i : Fin (witnessOrder p q)) :
    witnessFactorIndex p q (origin (witnessSeedPath p q) k i) = i := by
  have he : p + (k - p) = k := by omega
  simpa only [he] using witness_factor_origin_after p q (k - p) i

lemma witness_factor_pivot (p q : ℕ) (k : Fin (witnessOrder p q)) :
    witnessFactorIndex p q (origin (witnessSeedPath p q) k.val (witnessSeedPath p q k)) = k := by
  by_cases hk : k.val ≤ p
  · apply Fin.ext
    rw [witness_factor_origin_small p q k.val hk]
    simp only [witnessSeedPath, if_pos hk, Fin.val_mk,
      not_lt_of_ge hk, if_false, if_true]
  · rw [witness_factor_origin_ge p q k.val (by omega),
      witness_seed_ge p q k (by omega)]

lemma witness_factor_active (p q : ℕ) (k i : Fin (witnessOrder p q)) (hki : k ≤ i) :
    k ≤ witnessFactorIndex p q (origin (witnessSeedPath p q) k.val i) := by
  by_cases hk : k.val ≤ p
  · change k.val ≤ (witnessFactorIndex p q (origin (witnessSeedPath p q) k.val i)).val
    rw [witness_factor_origin_small p q k.val hk i]
    have hki' : k.val ≤ i.val := hki
    split_ifs <;> omega
  · rw [witness_factor_origin_ge p q k.val (by omega)]
    exact hki

#print axioms witness_prefix_order
#assert_trust kernel witness_prefix_order
#print axioms witness_factor_pivot
#assert_trust kernel witness_factor_pivot

end NLA.IE13
