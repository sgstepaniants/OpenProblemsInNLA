/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Exact odd-part reduction and compression of its square to a polynomial in X².
-/
import NLA.MF02.Errors
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Operations

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF02
open Polynomial

noncomputable def oddPart (p : ℝ[X]) : ℝ[X] :=
  (1 / 2 : ℝ) • (p - p.comp (-X))

lemma oddPart_eval (p : ℝ[X]) (x : ℝ) :
    (oddPart p).eval x = (p.eval x - p.eval (-x)) / 2 := by
  simp only [oddPart, eval_smul, eval_sub, eval_comp, eval_neg, eval_X, smul_eq_mul]
  ring

lemma oddPart_zero (p : ℝ[X]) : (oddPart p).eval 0 = 0 := by
  simp [oddPart_eval]

lemma oddPart_comp_neg (p : ℝ[X]) : (oddPart p).comp (-X) = -oddPart p := by
  simp only [oddPart, smul_comp, sub_comp, comp_neg_X_comp_neg_X]
  module

lemma oddPart_odd (p : ℝ[X]) (x : ℝ) :
    (oddPart p).eval (-x) = -(oddPart p).eval x := by
  simp only [oddPart_eval, neg_neg]
  ring

lemma oddPart_degree_le (p : ℝ[X]) : (oddPart p).natDegree ≤ p.natDegree := by
  calc
    (oddPart p).natDegree ≤ (p - p.comp (-X)).natDegree := natDegree_smul_le _ _
    _ ≤ max p.natDegree (p.comp (-X)).natDegree := natDegree_sub_le _ _
    _ = p.natDegree := by simp [natDegree_comp]

lemma oddPart_error_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ Set.Icc δ 1) :
    |(oddPart p).eval x - 1| ≤ uniformError δ p := by
  have hxpos : 0 < x := hδ0.trans_le hx.1
  have hp := eval_error_le hδ0 hδ1 p (Or.inr hx)
  have hn : -x ∈ gapDomain δ := Or.inl ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hm := eval_error_le hδ0 hδ1 p hn
  rw [Real.sign_of_pos hxpos, abs_le] at hp
  rw [Real.sign_of_neg (neg_neg_of_pos hxpos), sub_neg_eq_add, abs_le] at hm
  rw [oddPart_eval, abs_le]
  constructor <;> linarith

lemma odd_coeff_eq_zero_of_comp_neg {f : ℝ[X]} (hf : f.comp (-X) = f)
    {n : ℕ} (hn : ¬2 ∣ n) : f.coeff n = 0 := by
  have hodd : Odd n := Nat.not_even_iff_odd.mp (fun he => hn he.two_dvd)
  have hpow : (-1 : ℝ) ^ n = -1 := hodd.neg_one_pow
  have heq := congrArg (fun q : ℝ[X] => q.coeff n) hf
  have hX : (-X : ℝ[X]) = C (-1) * X := by simp
  rw [hX, comp_C_mul_X_coeff, hpow] at heq
  linarith

lemma expand_contract_even {f : ℝ[X]} (hf : f.comp (-X) = f) :
    expand ℝ 2 (contract 2 f) = f := by
  ext n
  rw [coeff_expand (by decide)]
  by_cases hn : 2 ∣ n
  · rw [if_pos hn, coeff_contract (by decide), Nat.div_mul_cancel hn]
  · rw [if_neg hn]
    exact (odd_coeff_eq_zero_of_comp_neg hf hn).symm

noncomputable def oddSquarePolynomial (p : ℝ[X]) : ℝ[X] :=
  contract 2 (oddPart p ^ 2)

lemma oddSquare_expand (p : ℝ[X]) : expand ℝ 2 (oddSquarePolynomial p) = oddPart p ^ 2 := by
  apply expand_contract_even
  rw [pow_comp, oddPart_comp_neg]
  ring

lemma oddSquare_eval (p : ℝ[X]) (x : ℝ) :
    (oddSquarePolynomial p).eval (x ^ 2) = (oddPart p).eval x ^ 2 := by
  have h := congrArg (fun q : ℝ[X] => q.eval x) (oddSquare_expand p)
  simpa only [expand_eval, eval_pow] using h

lemma oddSquare_zero (p : ℝ[X]) : (oddSquarePolynomial p).eval 0 = 0 := by
  simpa [oddPart_zero] using oddSquare_eval p 0

lemma oddSquare_degree_le (p : ℝ[X]) : (oddSquarePolynomial p).natDegree ≤ p.natDegree := by
  have h := congrArg (fun q : ℝ[X] => q.natDegree) (oddSquare_expand p)
  rw [natDegree_expand] at h
  have hp : (oddPart p ^ 2).natDegree ≤ 2 * (oddPart p).natDegree := natDegree_pow_le
  have ho := oddPart_degree_le p
  omega

end NLA.MF02
