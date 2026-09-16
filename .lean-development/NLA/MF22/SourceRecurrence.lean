/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The complete finite Toeplitz equation is equivalent to the literal transfer
recurrence. Inversion is confined to the proved nonsingular leading block.
-/
import NLA.MF22.SourceRows
import NLA.MF22.LeadingBlock

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open scoped BigOperators

lemma leading_solve_eq (ρ : ℝ) (hρ : 0 < ρ) (v b : Fin 2 → ℂ) :
    Matrix.mulVec (leadingBlock ρ) v = b ↔
      v = Matrix.mulVec (leadingBlock ρ)⁻¹ b := by
  have hleft := (leading_block_invertible ρ hρ).2.2.2
  have hright := (leading_block_invertible ρ hρ).2.2.1
  constructor
  · intro h
    have he := congrArg (Matrix.mulVec (leadingBlock ρ)⁻¹) h
    simpa only [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec] using he
  · intro h
    rw [h, Matrix.mulVec_mulVec, hright, Matrix.one_mulVec]

lemma source_block_equation {n : ℕ} (ρ : ℝ) (x : BlockVector n) (j : Fin n) :
    (fun c : Fin 2 => Matrix.mulVec (scaledToeplitz ρ n) x (j, c)) =
      Matrix.mulVec (leadingBlock ρ)
        ![coordinate x ((j.val : ℤ) + 1) 0, coordinate x (j.val : ℤ) 1] -
      Matrix.mulVec (transferRhs ρ) (sourceState x j.val) := by
  ext c
  fin_cases c
  · rw [source_row_zero]
    simp [leadingBlock, transferRhs, sourceState, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail] <;> ring
  · rw [source_row_one]
    simp [leadingBlock, transferRhs, sourceState, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.vecHead, Matrix.vecTail] <;> ring

lemma transfer_forcing_apply (ρ : ℝ) (w : Fin 4 → ℂ) (f : Fin 2 → ℂ) :
    Matrix.mulVec (transferMatrix ρ) w + Matrix.mulVec (forcingMatrix ρ) f =
      ![Matrix.mulVec (leadingBlock ρ)⁻¹ (Matrix.mulVec (transferRhs ρ) w + f) 0,
        Matrix.mulVec (leadingBlock ρ)⁻¹ (Matrix.mulVec (transferRhs ρ) w + f) 1,
        w 0, w 1] := by
  ext i
  fin_cases i <;>
    simp [transferMatrix, forcingMatrix, Matrix.mulVec, Matrix.mul_apply,
      dotProduct, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;> ring

lemma source_step_iff {n : ℕ} (ρ : ℝ) (hρ : 0 < ρ)
    (x : BlockVector n) (j : Fin n) (f : Fin 2 → ℂ) :
    (fun c : Fin 2 => Matrix.mulVec (scaledToeplitz ρ n) x (j, c)) = f ↔
      sourceState x (j.val + 1) =
        Matrix.mulVec (transferMatrix ρ) (sourceState x j.val) +
          Matrix.mulVec (forcingMatrix ρ) f := by
  rw [source_block_equation, transfer_forcing_apply]
  let v : Fin 2 → ℂ :=
    ![coordinate x ((j.val : ℤ) + 1) 0, coordinate x (j.val : ℤ) 1]
  let b : Fin 2 → ℂ := Matrix.mulVec (transferRhs ρ) (sourceState x j.val) + f
  have hsolve :
      Matrix.mulVec (leadingBlock ρ) v -
        Matrix.mulVec (transferRhs ρ) (sourceState x j.val) = f ↔
      v = Matrix.mulVec (leadingBlock ρ)⁻¹ b := by
    rw [sub_eq_iff_eq_add, add_comm f]
    exact leading_solve_eq ρ hρ v b
  change (Matrix.mulVec (leadingBlock ρ) v -
      Matrix.mulVec (transferRhs ρ) (sourceState x j.val) = f) ↔ _
  rw [hsolve]
  constructor
  · intro h
    ext i
    fin_cases i
    · simpa [v, sourceState, Nat.cast_add] using congrFun h 0
    · simpa [v, sourceState, Nat.cast_add] using congrFun h 1
    · simp [sourceState, Nat.cast_add, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
    · simp [sourceState, Nat.cast_add, Matrix.cons_val_two,
        Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail] <;>
        congr 1 <;> omega
  · intro h
    ext c
    fin_cases c
    · simpa [v, sourceState, Nat.cast_add] using congrFun h 0
    · simpa [v, sourceState, Nat.cast_add] using congrFun h 1

theorem source_recurrence (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ) (hn : 1 ≤ n)
    (x f : BlockVector n) :
    Matrix.mulVec (scaledToeplitz ρ n) x = f ↔
      ∀ j : Fin n, sourceState x (j.val + 1) =
        Matrix.mulVec (transferMatrix ρ) (sourceState x j.val) +
          Matrix.mulVec (forcingMatrix ρ) (fun c : Fin 2 => f (j, c)) := by
  constructor
  · intro h j
    apply (source_step_iff ρ hρ x j (fun c => f (j, c))).mp
    rw [h]
  · intro h
    funext row
    obtain ⟨j, c⟩ := row
    exact congrFun ((source_step_iff ρ hρ x j (fun d => f (j, d))).mpr (h j)) c

#assert_trust kernel source_recurrence
#print axioms source_recurrence

end NLA.MF22
