/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Constructive composition bounds and a direct infimum-approximation argument.
-/
import NLA.MF02.Errors

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF02
open Polynomial

lemma cubic_iteration_exists (T : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ a : ℝ, ∃ p : ℝ[X], 0 < a ∧ a < 1 ∧ CubicComposition T p ∧
      (∀ x ∈ Set.Icc δ 1, a ≤ p.eval x ∧ p.eval x ≤ 1) ∧
      gapRatio a ≤ gapRatio δ ^ (2 ^ T) := by
  induction T with
  | zero =>
      refine ⟨δ, X, hδ0, hδ1, CubicComposition.empty, ?_, ?_⟩
      · intro x hx
        simpa only [eval_X] using hx
      · simp
  | succ T ih =>
      obtain ⟨a, p, ha0, ha1, hp, himage, hr⟩ := ih
      have hinterval := optimized_cubic_interval a ha0 ha1
      refine ⟨improvedGap a,
        C (cubicA a / cubicScale a) * p + C (-1 / cubicScale a) * p ^ 3,
        hinterval.2.1, hinterval.2.2.1,
        CubicComposition.stage hp _ _, ?_, ?_⟩
      · intro x hx
        have h := hinterval.2.2.2 (p.eval x) (himage x hx)
        simpa only [optimizedCubic, cubic, eval_add, eval_mul, eval_C, eval_X, eval_pow] using h
      · calc
          gapRatio (improvedGap a) ≤ gapRatio a ^ 2 := optimized_cubic_ratio a ha0 ha1
          _ ≤ (gapRatio δ ^ (2 ^ T)) ^ 2 :=
            pow_le_pow_left₀ (gapRatio_pos ha0 ha1).le hr 2
          _ = gapRatio δ ^ (2 ^ (T + 1)) := by rw [← pow_mul, pow_succ]

lemma cubicError_upper_bound (T : ℕ) (hT : 1 ≤ T)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    cubicError T δ ≤ gapRatio δ ^ (2 ^ T) := by
  obtain ⟨a, p, ha0, ha1, hp, himage, hr⟩ := cubic_iteration_exists T δ hδ0 hδ1
  calc
    cubicError T δ ≤ uniformError δ (C (2 / (1 + a)) * p) :=
      cubicError_le hδ0 hδ1 (cubicComposition_scale hT hp _)
    _ ≤ gapRatio a := centered_polynomial_error hδ0 hδ1 ha0 p (cubicComposition_odd hp) himage
    _ ≤ gapRatio δ ^ (2 ^ T) := hr

lemma gapRatio_involution {a : ℝ} (ha : 0 < a) : gapRatio (gapRatio a) = a := by
  have hd : 1 + a ≠ 0 := by positivity
  unfold gapRatio
  field_simp [hd]
  ring

lemma cubic_improve_error {T : ℕ} {δ e : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {p : ℝ[X]} (hp : CubicComposition T p) (he0 : 0 < e) (he1 : e < 1)
    (he : uniformError δ p ≤ e) :
    ∃ q : ℝ[X], CubicComposition (T + 1) q ∧ uniformError δ q ≤ e ^ 2 := by
  let a := gapRatio e
  have ha0 : 0 < a := gapRatio_pos he0 he1
  have ha1 : a < 1 := gapRatio_lt_one he0
  have hden : 0 < 1 + e := by linarith
  let c := cubicA a / cubicScale a
  let d := -1 / cubicScale a
  let f : ℝ[X] := C (c / (1 + e)) * p + C (d / (1 + e) ^ 3) * p ^ 3
  have hf : CubicComposition (T + 1) f := CubicComposition.stage hp _ _
  have heval (x : ℝ) : f.eval x = (optimizedCubic a).eval (p.eval x / (1 + e)) := by
    dsimp [f, c, d]
    simp only [optimizedCubic, cubic, eval_add, eval_mul, eval_C, eval_X, eval_pow]
    ring
  have hinterval := optimized_cubic_interval a ha0 ha1
  have himage : ∀ x ∈ Set.Icc δ 1, improvedGap a ≤ f.eval x ∧ f.eval x ≤ 1 := by
    intro x hx
    have hxpos : 0 < x := hδ0.trans_le hx.1
    have hpbound := (eval_error_le hδ0 hδ1 p (Or.inr hx)).trans he
    rw [Real.sign_of_pos hxpos, abs_le] at hpbound
    have hscaled : p.eval x / (1 + e) ∈ Set.Icc a 1 := by
      constructor
      · exact div_le_div_of_nonneg_right (by linarith [hpbound.1]) hden.le
      · exact (div_le_one hden).mpr (by linarith [hpbound.2])
    rw [heval]
    exact hinterval.2.2.2 _ hscaled
  refine ⟨C (2 / (1 + improvedGap a)) * f,
    cubicComposition_scale (by omega) hf _, ?_⟩
  calc
    uniformError δ (C (2 / (1 + improvedGap a)) * f) ≤ gapRatio (improvedGap a) :=
      centered_polynomial_error hδ0 hδ1 hinterval.2.1 f (cubicComposition_odd hf) himage
    _ ≤ gapRatio a ^ 2 := optimized_cubic_ratio a ha0 ha1
    _ = e ^ 2 := by dsimp [a]; rw [gapRatio_involution he0]

/-- A smaller-than-minimum contradiction chooses an error tolerance strictly
between the infimum and min(1,sqrt(C_next)). No minimizing tuple is assumed. -/
lemma cubicError_square_step (T : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hc0 : 0 < cubicError T δ) (hc1 : cubicError T δ < 1) :
    cubicError (T + 1) δ ≤ cubicError T δ ^ 2 := by
  by_contra h
  have hlt : cubicError T δ ^ 2 < cubicError (T + 1) δ := lt_of_not_ge h
  have hn0 : 0 ≤ cubicError (T + 1) δ := cubicError_nonneg _ hδ0 hδ1
  have hs := Real.sq_sqrt hn0
  have hsnonneg := Real.sqrt_nonneg (cubicError (T + 1) δ)
  have hroot : cubicError T δ < Real.sqrt (cubicError (T + 1) δ) := by nlinarith
  obtain ⟨e, hce, he⟩ := exists_between (lt_min hc1 hroot)
  have he0 : 0 < e := hc0.trans hce
  have he1 : e < 1 := (lt_min_iff.mp he).1
  have hesq : e ^ 2 < cubicError (T + 1) δ := by
    have he' := (lt_min_iff.mp he).2
    nlinarith
  obtain ⟨v, ⟨p, hp, rfl⟩, hpv⟩ :=
    exists_lt_of_csInf_lt (cubic_error_set_nonempty T δ) hce
  obtain ⟨q, hq, hqerror⟩ := cubic_improve_error hδ0 hδ1 hp he0 he1 hpv.le
  have hmin := cubicError_le hδ0 hδ1 hq
  linarith

lemma cubicError_lt_one (T : ℕ) (hT : 1 ≤ T)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) : cubicError T δ < 1 :=
  (cubicError_upper_bound T hT δ hδ0 hδ1).trans_lt
    (pow_lt_one₀ (gapRatio_pos hδ0 hδ1).le (gapRatio_lt_one hδ0) (by positivity))

lemma cubicError_first_strict {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    cubicError 1 δ < cubicError 0 δ := by
  have hr0 := gapRatio_pos hδ0 hδ1
  have hr1 := gapRatio_lt_one hδ0
  have hless : gapRatio δ < 1 - δ := by
    unfold gapRatio
    apply (div_lt_iff₀ (show 0 < 1 + δ by linarith)).mpr
    nlinarith
  have hsquare : gapRatio δ ^ 2 < gapRatio δ := by nlinarith
  rw [cubicError_zero hδ0 hδ1]
  exact (cubicError_upper_bound 1 (by decide) δ hδ0 hδ1).trans_lt
    (by simpa using hsquare.trans hless)

end NLA.MF02
