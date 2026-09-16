/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.

Polynomial matrix evaluation on a left or right eigenmatrix. These exact
identities will project the actual singular-pencil adjugate on both sides.
-/
import NLA.MF22.Definitions
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF22
open Polynomial

lemma power_mul_of_eigenmatrix {n : ℕ} (T A : Square n) (z : ℂ)
    (h : T * A = z • A) (k : ℕ) : T ^ k * A = z ^ k • A := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Matrix.mul_assoc, ih, Matrix.mul_smul, h, smul_smul, pow_succ]

lemma mul_power_of_eigenmatrix {n : ℕ} (T A : Square n) (z : ℂ)
    (h : A * T = z • A) (k : ℕ) : A * T ^ k = z ^ k • A := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.smul_mul, h, smul_smul, pow_succ]

lemma aeval_mul_of_eigenmatrix {n : ℕ} (T A : Square n) (z : ℂ)
    (h : T * A = z • A) (p : ℂ[X]) : aeval T p * A = p.eval z • A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Matrix.add_mul, hp, hq, eval_add, add_smul]
  | monomial k c =>
      rw [aeval_monomial, Matrix.mul_assoc, power_mul_of_eigenmatrix T A z h k]
      simp only [← Algebra.smul_def, smul_smul, eval_monomial]

lemma mul_aeval_of_eigenmatrix {n : ℕ} (T A : Square n) (z : ℂ)
    (h : A * T = z • A) (p : ℂ[X]) : A * aeval T p = p.eval z • A := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Matrix.mul_add, hp, hq, eval_add, add_smul]
  | monomial k c =>
      rw [aeval_monomial, ← Matrix.mul_assoc, ← Algebra.commutes c A,
        Matrix.mul_assoc, mul_power_of_eigenmatrix T A z h k]
      simp only [← Algebra.smul_def, smul_smul, eval_monomial]

#assert_trust kernel aeval_mul_of_eigenmatrix
#assert_trust kernel mul_aeval_of_eigenmatrix

end NLA.MF22
