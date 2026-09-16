/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Exact unitary conjugation and positive real scaling preserve the full pencil
extremum property, with every Hermitian diagonal block still quantified.
-/
import NLA.MI04.BlockSymmetry

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04

section FiniteCoordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma unitarySimilarity_neg (M : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) :
    unitarySimilarity (-M) U = -unitarySimilarity M U := by
  simp [unitarySimilarity]

lemma unitarySimilarity_inverse (M : CMatrix ι) (U : Matrix.unitaryGroup ι ℂ) :
    unitarySimilarity (unitarySimilarity M (star U)) U = M := by
  unfold unitarySimilarity
  simp only [Unitary.coe_star, ← Matrix.star_eq_conjTranspose, star_star]
  calc
    star (U : CMatrix ι) * ((U : CMatrix ι) * M * star (U : CMatrix ι)) *
        (U : CMatrix ι) =
      (star (U : CMatrix ι) * (U : CMatrix ι)) * M *
        (star (U : CMatrix ι) * (U : CMatrix ι)) := by noncomm_ring
    _ = M := by rw [Unitary.coe_star_mul_self, one_mul, mul_one]

variable [Nonempty ι]

lemma topValue_real_smul (M : CMatrix ι) (r : ℝ) (hr : 0 ≤ r) :
    topValue ((r : ℂ) • M) = r * topValue M := by
  apply le_antisymm
  · apply (topValue_le_iff _ _).mpr
    intro v hv
    rw [realQuadratic_smul_matrix]
    exact mul_le_mul_of_nonneg_left (realQuadratic_le_top_of_unit M v hv) hr
  · obtain ⟨u, hu, he, _⟩ := topValue_attained M
    have h := realQuadratic_le_top_of_unit ((r : ℂ) • M) u hu
    simpa only [realQuadratic_smul_matrix, he] using h

end FiniteCoordinates

def blockUnitary {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix.unitaryGroup (Fin n ⊕ Fin n) ℂ := by
  refine ⟨Matrix.fromBlocks (U : Square n) 0 0 (U : Square n), ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.fromBlocks_conjTranspose]
  have hu : (U : Square n) * (U : Square n).conjTranspose = 1 := U.property.2
  simp [Matrix.fromBlocks_multiply, hu, Matrix.fromBlocks_one]

lemma pencil_unitarySimilarity {n : ℕ} (X T : Square n)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    unitarySimilarity (pencil X T) (blockUnitary U) =
      pencil (unitarySimilarity X U) (unitarySimilarity T U) := by
  simp [unitarySimilarity, pencil, completion, blockUnitary,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

lemma extreme_symmetry_unitary {n : ℕ} (hn : 1 ≤ n) (X : Square n)
    (hX : ExtremeSymmetry X) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    ExtremeSymmetry (unitarySimilarity X U) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  intro T hT
  let T0 : Square n := unitarySimilarity T (star U)
  have hT0 : T0.IsHermitian := unitarySimilarity_isHermitian T hT (star U)
  have hTback : unitarySimilarity T0 U = T := unitarySimilarity_inverse T U
  have hleft := topValue_unitarySimilarity (pencil X T0) (blockUnitary U)
  rw [pencil_unitarySimilarity, hTback] at hleft
  have hright := topValue_unitarySimilarity (-pencil X T0) (blockUnitary U)
  rw [unitarySimilarity_neg, pencil_unitarySimilarity, hTback] at hright
  exact hleft.trans ((hX T0 hT0).trans hright.symm)

lemma pencil_real_smul {n : ℕ} (X T : Square n) (r : ℝ) :
    pencil ((r : ℂ) • X) ((r : ℂ) • T) = (r : ℂ) • pencil X T := by
  simp [pencil, completion, Matrix.fromBlocks_smul, Matrix.conjTranspose_smul]

lemma extreme_symmetry_positive_scale {n : ℕ} (hn : 1 ≤ n) (X : Square n)
    (hX : ExtremeSymmetry X) (r : ℝ) (hr : 0 < r) :
    ExtremeSymmetry ((r : ℂ) • X) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  intro T hT
  let T0 : Square n := ((r⁻¹ : ℝ) : ℂ) • T
  have hT0 : T0.IsHermitian := hermitian_real_smul T hT r⁻¹
  have hscale : (r : ℂ) • T0 = T := by
    dsimp [T0]
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hr.ne', Complex.ofReal_one,
      one_smul]
  have he : pencil ((r : ℂ) • X) T = (r : ℂ) • pencil X T0 := by
    calc
      pencil ((r : ℂ) • X) T = pencil ((r : ℂ) • X) ((r : ℂ) • T0) :=
        congrArg (pencil ((r : ℂ) • X)) hscale.symm
      _ = (r : ℂ) • pencil X T0 := pencil_real_smul X T0 r
  rw [he, ← smul_neg, topValue_real_smul _ r hr.le, topValue_real_smul _ r hr.le]
  exact congrArg (fun x : ℝ => r * x) (hX T0 hT0)

theorem extreme_symmetry_scaled_unitary {n : ℕ} (hn : 1 ≤ n) (X : Square n)
    (hX : ExtremeSymmetry X) (r : ℝ) (hr : 0 < r)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    ExtremeSymmetry ((r : ℂ) • unitarySimilarity X U) :=
  extreme_symmetry_positive_scale hn (unitarySimilarity X U)
    (extreme_symmetry_unitary hn X hX U) r hr

#print axioms extreme_symmetry_scaled_unitary
#assert_trust kernel extreme_symmetry_scaled_unitary

end NLA.MI04
