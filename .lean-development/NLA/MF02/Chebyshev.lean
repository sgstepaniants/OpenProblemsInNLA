/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
The exterior comparison is reused from Mathlib's Yuval Filmus development.
The endpoint evaluation uses an exact recurrence instead of logarithms/cosh.
-/
import NLA.MF02.Parity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF02
open Polynomial

lemma chebyshev_joukowski (r : ℝ) (hr : r ≠ 0) (D : ℕ) :
    (Chebyshev.T ℝ (D : ℤ)).eval ((r + r⁻¹) / 2) =
      (r ^ D + (r ^ D)⁻¹) / 2 := by
  induction D using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n hn hn1 =>
      have hc1 : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by omega
      have hc2 : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by omega
      have hrec := congrArg (fun p : ℝ[X] => p.eval ((r + r⁻¹) / 2))
        (Chebyshev.T_add_two ℝ (n : ℤ))
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at hrec
      rw [← hc1, ← hc2, hn, hn1] at hrec
      rw [hrec]
      simp only [pow_add, pow_succ, pow_zero, one_mul]
      field_simp [hr]
      ring

lemma chebyshev_exterior_le (D : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ D)
    (hb : ∀ x ∈ Set.Icc (-1) 1, |p.eval x| ≤ 1)
    (x : ℝ) (hx : 1 ≤ x) : p.eval x ≤ (Chebyshev.T ℝ (D : ℤ)).eval x := by
  simpa using Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one
    (n := D) (P := p) (k := 0) hx (natDegree_le_iff_degree_le.mp hp) hb

lemma scalar_error_from_chebyshev {e t : ℝ} (he0 : 0 < e) (he1 : e < 1)
    (ht0 : 0 < t) (ht1 : t < 1)
    (h : (1 + e ^ 2) / (2 * e) ≤ (t + t⁻¹) / 2) : t ≤ e := by
  have h1 := (div_le_iff₀ (show 0 < 2 * e by positivity)).mp h
  have h2 := mul_le_mul_of_nonneg_right h1 ht0.le
  have heq : ((t + t⁻¹) / 2 * (2 * e)) * t = e * (t ^ 2 + 1) := by
    field_simp [ne_of_gt ht0]
    ring
  rw [heq] at h2
  by_contra hnot
  have hte : e < t := lt_of_not_ge hnot
  have hpos : 0 < (t - e) * (1 - e * t) := by
    apply mul_pos (sub_pos.mpr hte)
    nlinarith
  nlinarith

/-- This lemma works with any strict error tolerance e, so the final lower
bound needs no special argument assuming a positive attained error. -/
lemma strict_tolerance_degree_bound (δ e : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (he0 : 0 < e) (he1 : e < 1) (D : ℕ) (hD : 1 ≤ D)
    (p : ℝ[X]) (hp : p.natDegree ≤ D) (he : uniformError δ p ≤ e) :
    gapRatio δ ^ D ≤ e := by
  let B := oddSquarePolynomial p
  let H : ℝ[X] := C ((1 + e ^ 2) / (2 * e)) - C (1 / (2 * e)) * B
  let F : ℝ[X] := C ((1 + δ ^ 2) / 2) - C ((1 - δ ^ 2) / 2) * X
  let R := H.comp F
  let γ := (1 + δ ^ 2) / (1 - δ ^ 2)
  have hδsq : δ ^ 2 < 1 := by nlinarith
  have hden : 0 < 1 - δ ^ 2 := by linarith
  have hevalH (t : ℝ) : H.eval t = (1 + e ^ 2 - B.eval t) / (2 * e) := by
    dsimp [H]
    simp only [eval_sub, eval_C, eval_mul]
    ring
  have hBdeg : B.natDegree ≤ D := (oddSquare_degree_le p).trans hp
  have hHdeg : H.natDegree ≤ D := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · simp
    · exact (natDegree_C_mul_le _ B).trans hBdeg
  have hFdeg : F.natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · simp
    · simpa using natDegree_C_mul_X_pow_le ((1 - δ ^ 2) / 2) 1
  have hRdeg : R.natDegree ≤ D := by
    calc
      R.natDegree ≤ H.natDegree * F.natDegree := natDegree_comp_le
      _ ≤ D * 1 := Nat.mul_le_mul hHdeg hFdeg
      _ = D := Nat.mul_one D
  have hHbound (t : ℝ) (ht : t ∈ Set.Icc (δ ^ 2) 1) : |H.eval t| ≤ 1 := by
    have ht0 : 0 ≤ t := (sq_nonneg δ).trans ht.1
    have hs := Real.sq_sqrt ht0
    have hs0 := Real.sqrt_nonneg t
    have hsδ : δ ≤ Real.sqrt t := by nlinarith [ht.1]
    have hs1 : Real.sqrt t ≤ 1 := by nlinarith [ht.2]
    have ho := (oddPart_error_le hδ0 hδ1 p ⟨hsδ, hs1⟩).trans he
    rw [abs_le] at ho
    have hB : B.eval t = (oddPart p).eval (Real.sqrt t) ^ 2 := by
      simpa only [hs] using oddSquare_eval p (Real.sqrt t)
    have hlow : (1 - e) ^ 2 ≤ (oddPart p).eval (Real.sqrt t) ^ 2 := by
      nlinarith [sq_nonneg ((oddPart p).eval (Real.sqrt t) - (1 - e))]
    have hhigh : (oddPart p).eval (Real.sqrt t) ^ 2 ≤ (1 + e) ^ 2 := by
      nlinarith [sq_nonneg ((1 + e) - (oddPart p).eval (Real.sqrt t))]
    rw [hevalH, hB, abs_le]
    constructor
    · apply (le_div_iff₀ (show 0 < 2 * e by positivity)).mpr
      nlinarith
    · apply (div_le_iff₀ (show 0 < 2 * e by positivity)).mpr
      nlinarith
  have hRbound : ∀ x ∈ Set.Icc (-1) 1, |R.eval x| ≤ 1 := by
    intro x hx
    have hF : F.eval x ∈ Set.Icc (δ ^ 2) 1 := by
      dsimp [F]
      simp only [eval_sub, eval_C, eval_mul, eval_X]
      constructor
      · nlinarith [mul_nonneg hden.le (show 0 ≤ 1 - x by linarith [hx.2])]
      · nlinarith [mul_nonneg hden.le (show 0 ≤ x + 1 by linarith [hx.1])]
    simpa only [R, eval_comp] using hHbound (F.eval x) hF
  have hγ : 1 ≤ γ := by
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hFzero : F.eval γ = 0 := by
    dsimp [F, γ]
    simp only [eval_sub, eval_C, eval_mul, eval_X]
    field_simp [ne_of_gt hden]
    ring
  have hRzero : R.eval γ = (1 + e ^ 2) / (2 * e) := by
    change (H.comp F).eval γ = _
    rw [eval_comp, hFzero, hevalH]
    simp [B, oddSquare_zero]
  have hγratio : γ = (gapRatio δ + (gapRatio δ)⁻¹) / 2 := by
    have hplus : 1 + δ ≠ 0 := by positivity
    have hminus : 1 - δ ≠ 0 := ne_of_gt (sub_pos.mpr hδ1)
    dsimp [γ, gapRatio]
    field_simp [ne_of_gt hden, hplus, hminus]
    ring
  have hcompare := chebyshev_exterior_le D R hRdeg hRbound γ hγ
  rw [hRzero, hγratio, chebyshev_joukowski _ (ne_of_gt (gapRatio_pos hδ0 hδ1)) D] at hcompare
  exact scalar_error_from_chebyshev he0 he1 (pow_pos (gapRatio_pos hδ0 hδ1) D)
    (pow_lt_one₀ (gapRatio_pos hδ0 hδ1).le (gapRatio_lt_one hδ0) (by omega)) hcompare

theorem degree_error_lower_bound (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (D : ℕ) (hD : 1 ≤ D) (p : ℝ[X]) (hp : p.natDegree ≤ D) :
    gapRatio δ ^ D ≤ uniformError δ p := by
  by_contra hnot
  have hlt : uniformError δ p < gapRatio δ ^ D := lt_of_not_ge hnot
  have hnonneg := uniformError_nonneg hδ0 hδ1 p
  obtain ⟨e, heleft, heright⟩ := exists_between hlt
  have he0 : 0 < e := hnonneg.trans_lt heleft
  have he1 : e < 1 := heright.trans
    (pow_lt_one₀ (gapRatio_pos hδ0 hδ1).le (gapRatio_lt_one hδ0) (by omega))
  have hbound := strict_tolerance_degree_bound δ e hδ0 hδ1 he0 he1 D hD p hp heleft.le
  exact (not_lt_of_ge hbound) heright

#assert_trust kernel degree_error_lower_bound
#print axioms degree_error_lower_bound

end NLA.MF02
