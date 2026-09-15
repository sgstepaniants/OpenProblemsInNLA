/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. AI-assisted formalization.
MF-02 program semantics and gate/degree accounting, with stored-value reuse.
-/
import NLA.MF02.Definitions
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

namespace NLA.MF02
open Polynomial

lemma freeSpan_degree_le {registers : List ℝ[X]} {D : ℕ}
    (h : ∀ p ∈ registers, p.natDegree ≤ D) {p : ℝ[X]}
    (hp : p ∈ freeSpan registers) : p.natDegree ≤ D := by
  have hs : freeSpan registers ≤ degreeLE ℝ (D : WithBot ℕ) := by
    apply Submodule.span_le.mpr
    intro q hq
    exact mem_degreeLE.mpr (natDegree_le_iff_degree_le.mp (h q hq))
  exact natDegree_le_iff_degree_le.mpr (mem_degreeLE.mp (hs hp))

lemma history_degree_bound {k : ℕ} {registers : List ℝ[X]}
    (h : ProductHistory k registers) : ∀ p ∈ registers, p.natDegree ≤ 2 ^ k := by
  induction h with
  | initial =>
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp
  | @product k registers a b history ha hb ih =>
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · have hda := freeSpan_degree_le ih ha
        have hdb := freeSpan_degree_le ih hb
        calc
          (a * b).natDegree ≤ a.natDegree + b.natDegree := natDegree_mul_le
          _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add hda hdb
          _ = 2 ^ (k + 1) := by rw [pow_succ]; omega
      · calc
          p.natDegree ≤ 2 ^ k := ih p hp
          _ ≤ 2 ^ (k + 1) := by rw [pow_succ]; omega

theorem program_degree_bound (m : ℕ) (p : ℝ[X])
    (hp : ProgramComputable m p) : p.natDegree ≤ 2 ^ m := by
  obtain ⟨k, hkm, registers, history, hp⟩ := hp
  exact (freeSpan_degree_le (history_degree_bound history) hp).trans
    (Nat.pow_le_pow_right (by decide) hkm)

lemma freeSpan_cons_mono (q : ℝ[X]) (registers : List ℝ[X]) :
    freeSpan registers ≤ freeSpan (q :: registers) := by
  apply Submodule.span_le.mpr
  intro p hp
  exact Submodule.subset_span (List.mem_cons_of_mem q hp)

lemma mem_freeSpan_of_mem {p : ℝ[X]} {registers : List ℝ[X]}
    (hp : p ∈ registers) : p ∈ freeSpan registers :=
  Submodule.subset_span hp

lemma programComputable_mono {m n : ℕ} (hmn : m ≤ n) {p : ℝ[X]}
    (hp : ProgramComputable m p) : ProgramComputable n p := by
  obtain ⟨k, hk, registers, hhistory, hp⟩ := hp
  exact ⟨k, hk.trans hmn, registers, hhistory, hp⟩

lemma programComputable_X (m : ℕ) : ProgramComputable m (X : ℝ[X]) := by
  refine ⟨0, Nat.zero_le m, [1, X], ProductHistory.initial, ?_⟩
  exact mem_freeSpan_of_mem (by simp)

lemma programComputable_linear (m : ℕ) (a b : ℝ) :
    ProgramComputable m (C a + C b * X) := by
  refine ⟨0, Nat.zero_le m, [1, X], ProductHistory.initial, ?_⟩
  have h1 : (1 : ℝ[X]) ∈ freeSpan [1, X] := mem_freeSpan_of_mem (by simp)
  have hX : (X : ℝ[X]) ∈ freeSpan [1, X] := mem_freeSpan_of_mem (by simp)
  have h := (freeSpan [1, X]).add_mem
    ((freeSpan [1, X]).smul_mem a h1) ((freeSpan [1, X]).smul_mem b hX)
  simpa only [smul_eq_C_mul, mul_one] using h

/-- Two new product gates compute p² and then p³. Neither p nor the square
is charged again when reused in the final free linear combination. -/
lemma programComputable_cubic {m : ℕ} {p : ℝ[X]}
    (hp : ProgramComputable m p) (a b : ℝ) :
    ProgramComputable (m + 2) (C a * p + C b * p ^ 3) := by
  obtain ⟨k, hk, registers, history, hp⟩ := hp
  have history1 : ProductHistory (k + 1) ((p * p) :: registers) :=
    ProductHistory.product history hp hp
  have hp1 : p ∈ freeSpan ((p * p) :: registers) :=
    freeSpan_cons_mono (p * p) registers hp
  have hsquare : p * p ∈ freeSpan ((p * p) :: registers) :=
    mem_freeSpan_of_mem (by simp)
  have history2 : ProductHistory (k + 2) (((p * p) * p) :: (p * p) :: registers) :=
    ProductHistory.product history1 hsquare hp1
  refine ⟨k + 2, by omega, _, history2, ?_⟩
  have hp2 : p ∈ freeSpan (((p * p) * p) :: (p * p) :: registers) :=
    freeSpan_cons_mono ((p * p) * p) ((p * p) :: registers) hp1
  have hcube : p ^ 3 ∈ freeSpan (((p * p) * p) :: (p * p) :: registers) := by
    have h : (p * p) * p ∈ freeSpan (((p * p) * p) :: (p * p) :: registers) :=
      mem_freeSpan_of_mem (by simp)
    simpa only [pow_succ, pow_zero, one_mul] using h
  simpa only [smul_eq_C_mul] using
    (freeSpan _).add_mem ((freeSpan _).smul_mem a hp2) ((freeSpan _).smul_mem b hcube)

theorem cubic_degree_and_cost (T : ℕ) (p : ℝ[X])
    (hp : CubicComposition T p) :
    p.natDegree ≤ 3 ^ T ∧ ProgramComputable (2 * T) p := by
  induction hp with
  | empty => exact ⟨by simp, programComputable_X 0⟩
  | @stage T p hp a b ih =>
      constructor
      · apply natDegree_add_le_of_degree_le
        · calc
            (C a * p).natDegree ≤ p.natDegree := natDegree_C_mul_le a p
            _ ≤ 3 ^ T := ih.1
            _ ≤ 3 ^ (T + 1) := by rw [pow_succ]; omega
        · calc
            (C b * p ^ 3).natDegree ≤ (p ^ 3).natDegree := natDegree_C_mul_le b _
            _ ≤ 3 * p.natDegree := natDegree_pow_le
            _ ≤ 3 * 3 ^ T := Nat.mul_le_mul_left 3 ih.1
            _ = 3 ^ (T + 1) := by rw [pow_succ, Nat.mul_comm]
      · simpa only [Nat.mul_add, Nat.mul_one] using programComputable_cubic ih.2 a b

lemma cubicComposition_identity (T : ℕ) : CubicComposition T (X : ℝ[X]) := by
  induction T with
  | zero => exact CubicComposition.empty
  | succ T ih =>
      simpa using CubicComposition.stage ih 1 0

lemma cubicComposition_odd {T : ℕ} {p : ℝ[X]} (hp : CubicComposition T p) :
    ∀ x : ℝ, p.eval (-x) = -p.eval x := by
  induction hp with
  | empty => intro x; simp
  | stage hp a b ih =>
      intro x
      simp only [eval_add, eval_mul, eval_C, eval_pow, ih]
      ring

lemma cubicComposition_scale {T : ℕ} {p : ℝ[X]} (hT : 1 ≤ T)
    (hp : CubicComposition T p) (c : ℝ) : CubicComposition T (C c * p) := by
  cases hp with
  | empty => omega
  | stage previous a b =>
      have h := CubicComposition.stage previous (c * a) (c * b)
      convert h using 1
      simp only [map_mul]
      ring

#assert_trust kernel program_degree_bound
#print axioms program_degree_bound
#assert_trust kernel cubic_degree_and_cost
#print axioms cubic_degree_and_cost

end NLA.MF02
