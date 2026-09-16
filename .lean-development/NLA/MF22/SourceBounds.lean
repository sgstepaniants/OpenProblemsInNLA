/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

The finitely many literal scalar block entries are checked exactly. Their
loose uniform bounds are sufficient for the eventual quadratic estimate.
-/
import NLA.MF22.Norms
import Mathlib.Tactic

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22

lemma blockB_abs_le (k : ℤ) (i j : Fin 2) : |blockB k i j| ≤ 2 := by
  unfold blockB
  split_ifs <;> fin_cases i <;> fin_cases j <;> norm_num [Matrix.smul_apply]

lemma blockC_abs_le (k : ℤ) (i j : Fin 2) : |blockC k i j| ≤ 1 := by
  unfold blockC
  split_ifs <;> fin_cases i <;> fin_cases j <;> norm_num [Matrix.smul_apply]

theorem source_entry_bound (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (r s : BlockIndex n) : ‖toeplitz ρ n r s‖ ≤ 2 + ρ := by
  let k : ℤ := (r.1.val : ℤ) - (s.1.val : ℤ)
  change ‖Complex.I * (blockB k r.2 s.2 : ℂ) -
    (ρ : ℂ) * (blockC k r.2 s.2 : ℂ)‖ ≤ 2 + ρ
  calc
    _ ≤ ‖Complex.I * (blockB k r.2 s.2 : ℂ)‖ +
        ‖(ρ : ℂ) * (blockC k r.2 s.2 : ℂ)‖ := norm_sub_le _ _
    _ = |blockB k r.2 s.2| + ρ * |blockC k r.2 s.2| := by
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    _ ≤ 2 + ρ * 1 := add_le_add (blockB_abs_le k r.2 s.2)
      (mul_le_mul_of_nonneg_left (blockC_abs_le k r.2 s.2) hρ.le)
    _ = 2 + ρ := by ring

#assert_trust kernel source_entry_bound
#print axioms source_entry_bound

end NLA.MF22
