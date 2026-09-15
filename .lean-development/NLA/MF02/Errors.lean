/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
Actual compact-domain maxima and nonempty bounded-below coefficient infima.
-/
import NLA.MF02.Model
import NLA.MF02.Cubic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF02
open Polynomial

lemma gapDomain_nonempty {δ : ℝ} (hδ1 : δ < 1) : (gapDomain δ).Nonempty :=
  ⟨δ, Or.inr ⟨le_rfl, hδ1.le⟩⟩

lemma error_image_compact (δ : ℝ) (hδ0 : 0 < δ) (p : ℝ[X]) :
    IsCompact ((fun x : ℝ => |p.eval x - Real.sign x|) '' gapDomain δ) := by
  have hneg : ContinuousOn (fun x : ℝ => |p.eval x - Real.sign x|)
      (Set.Icc (-1) (-δ)) := by
    have hc : Continuous (fun x : ℝ => |p.eval x + 1|) :=
      (p.continuous.add continuous_const).abs
    apply hc.continuousOn.congr
    intro x hx
    have hxneg : x < 0 := by linarith [hx.2]
    simp [Real.sign_of_neg hxneg]
  have hpos : ContinuousOn (fun x : ℝ => |p.eval x - Real.sign x|)
      (Set.Icc δ 1) := by
    have hc : Continuous (fun x : ℝ => |p.eval x - 1|) :=
      (p.continuous.sub continuous_const).abs
    apply hc.continuousOn.congr
    intro x hx
    have hxpos : 0 < x := hδ0.trans_le hx.1
    simp [Real.sign_of_pos hxpos]
  rw [gapDomain, Set.image_union]
  exact (isCompact_Icc.image_of_continuousOn hneg).union
    (isCompact_Icc.image_of_continuousOn hpos)

theorem uniform_error_is_maximum (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (p : ℝ[X]) :
    (∃ x ∈ gapDomain δ, uniformError δ p = |p.eval x - Real.sign x|) ∧
    (∀ x ∈ gapDomain δ, |p.eval x - Real.sign x| ≤ uniformError δ p) := by
  have hcompact := error_image_compact δ hδ0 p
  have hnonempty := (gapDomain_nonempty hδ1).image
    (fun x : ℝ => |p.eval x - Real.sign x|)
  have hmax := hcompact.isGreatest_sSup hnonempty
  obtain ⟨x, hx, heq⟩ := hmax.1
  exact ⟨⟨x, hx, heq.symm⟩, fun y hy => hmax.2 ⟨y, hy, rfl⟩⟩

lemma uniformError_nonneg {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (p : ℝ[X]) : 0 ≤ uniformError δ p := by
  obtain ⟨x, hx, heq⟩ := (uniform_error_is_maximum δ hδ0 hδ1 p).1
  rw [heq]
  exact abs_nonneg _

lemma eval_error_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (p : ℝ[X]) {x : ℝ} (hx : x ∈ gapDomain δ) :
    |p.eval x - Real.sign x| ≤ uniformError δ p :=
  (uniform_error_is_maximum δ hδ0 hδ1 p).2 x hx

lemma uniformError_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (p : ℝ[X]) {e : ℝ}
    (he : ∀ x ∈ gapDomain δ, |p.eval x - Real.sign x| ≤ e) :
    uniformError δ p ≤ e := by
  obtain ⟨x, hx, heq⟩ := (uniform_error_is_maximum δ hδ0 hδ1 p).1
  rw [heq]
  exact he x hx

lemma uniformError_odd_bound {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (p : ℝ[X]) (hodd : ∀ x : ℝ, p.eval (-x) = -p.eval x) {e : ℝ}
    (hpos : ∀ x ∈ Set.Icc δ 1, |p.eval x - 1| ≤ e) :
    uniformError δ p ≤ e := by
  apply uniformError_le hδ0 hδ1 p
  intro x hx
  rcases hx with hx | hx
  · have hxneg : x < 0 := by linarith [hx.2]
    have hn : -x ∈ Set.Icc δ 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have h := hpos (-x) hn
    have heq : p.eval (-x) - 1 = -(p.eval x + 1) := by rw [hodd]; ring
    rw [heq, abs_neg] at h
    simpa [Real.sign_of_neg hxneg] using h
  · simpa [Real.sign_of_pos (hδ0.trans_le hx.1)] using hpos x hx

lemma unrestricted_error_set_nonempty (m : ℕ) (δ : ℝ) :
    (uniformError δ '' {p : ℝ[X] | ProgramComputable m p}).Nonempty :=
  ⟨uniformError δ X, X, programComputable_X m, rfl⟩

lemma cubic_error_set_nonempty (T : ℕ) (δ : ℝ) :
    (uniformError δ '' {p : ℝ[X] | CubicComposition T p}).Nonempty :=
  ⟨uniformError δ X, X, cubicComposition_identity T, rfl⟩

lemma unrestricted_error_set_bddBelow (m : ℕ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    BddBelow (uniformError δ '' {p : ℝ[X] | ProgramComputable m p}) := by
  refine ⟨0, ?_⟩
  rintro e ⟨p, hp, rfl⟩
  exact uniformError_nonneg hδ0 hδ1 p

lemma cubic_error_set_bddBelow (T : ℕ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    BddBelow (uniformError δ '' {p : ℝ[X] | CubicComposition T p}) := by
  refine ⟨0, ?_⟩
  rintro e ⟨p, hp, rfl⟩
  exact uniformError_nonneg hδ0 hδ1 p

lemma unrestrictedError_le {m : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {p : ℝ[X]} (hp : ProgramComputable m p) :
    unrestrictedError m δ ≤ uniformError δ p :=
  csInf_le (unrestricted_error_set_bddBelow m hδ0 hδ1) ⟨p, hp, rfl⟩

lemma cubicError_le {T : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {p : ℝ[X]} (hp : CubicComposition T p) :
    cubicError T δ ≤ uniformError δ p :=
  csInf_le (cubic_error_set_bddBelow T hδ0 hδ1) ⟨p, hp, rfl⟩

lemma le_unrestrictedError (m : ℕ) (δ e : ℝ)
    (h : ∀ p : ℝ[X], ProgramComputable m p → e ≤ uniformError δ p) :
    e ≤ unrestrictedError m δ := by
  apply le_csInf (unrestricted_error_set_nonempty m δ)
  rintro y ⟨p, hp, rfl⟩
  exact h p hp

lemma le_cubicError (T : ℕ) (δ e : ℝ)
    (h : ∀ p : ℝ[X], CubicComposition T p → e ≤ uniformError δ p) :
    e ≤ cubicError T δ := by
  apply le_csInf (cubic_error_set_nonempty T δ)
  rintro y ⟨p, hp, rfl⟩
  exact h p hp

lemma unrestrictedError_nonneg (m : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ unrestrictedError m δ :=
  le_unrestrictedError m δ 0 (fun p _ => uniformError_nonneg hδ0 hδ1 p)

lemma cubicError_nonneg (T : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ cubicError T δ :=
  le_cubicError T δ 0 (fun p _ => uniformError_nonneg hδ0 hδ1 p)

lemma uniformError_X {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    uniformError δ X = 1 - δ := by
  apply le_antisymm
  · apply uniformError_odd_bound hδ0 hδ1 X (by intro x; simp)
    intro x hx
    simp only [eval_X]
    rw [abs_of_nonpos (by linarith [hx.2])]
    linarith [hx.1]
  · have h := eval_error_le hδ0 hδ1 X (x := δ) (Or.inr ⟨le_rfl, hδ1.le⟩)
    simpa [Real.sign_of_pos hδ0, abs_of_neg (sub_neg.mpr hδ1)] using h

lemma cubicError_zero {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    cubicError 0 δ = 1 - δ := by
  apply le_antisymm
  · exact (cubicError_le hδ0 hδ1 CubicComposition.empty).trans_eq
      (uniformError_X hδ0 hδ1)
  · apply le_cubicError
    intro p hp
    cases hp
    exact (uniformError_X hδ0 hδ1).ge

lemma centered_value_error {a x : ℝ} (ha : 0 < a) (hax : a ≤ x) (hx1 : x ≤ 1) :
    |2 * x / (1 + a) - 1| ≤ gapRatio a := by
  have hd : 0 < 1 + a := by linarith
  have heq : 2 * x / (1 + a) - 1 = (2 * x - (1 + a)) / (1 + a) := by
    field_simp [ne_of_gt hd]
    ring
  rw [heq, abs_le]
  constructor
  · have h := div_le_div_of_nonneg_right (show -(1 - a) ≤ 2 * x - (1 + a) by linarith) hd.le
    simpa only [neg_div, gapRatio] using h
  · exact div_le_div_of_nonneg_right (by linarith) hd.le

lemma centered_polynomial_error {δ a : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (ha : 0 < a) (p : ℝ[X]) (hodd : ∀ x : ℝ, p.eval (-x) = -p.eval x)
    (himage : ∀ x ∈ Set.Icc δ 1, a ≤ p.eval x ∧ p.eval x ≤ 1) :
    uniformError δ (C (2 / (1 + a)) * p) ≤ gapRatio a := by
  apply uniformError_odd_bound hδ0 hδ1 _
  · intro x
    simp only [eval_mul, eval_C, hodd]
    ring
  · intro x hx
    have h := centered_value_error ha (himage x hx).1 (himage x hx).2
    simpa only [eval_mul, eval_C, div_mul_eq_mul_div] using h

#assert_trust kernel uniform_error_is_maximum
#print axioms uniform_error_is_maximum

end NLA.MF02
