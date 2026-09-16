/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Literal complex quadratic forms and the genuine Euclidean operator norm.
-/
import NLA.MI04.Definitions
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic
import LeanCert.Tactic.Verification

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04
section FiniteCoordinates
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma realQuadratic_eq_reApply (M : CMatrix ι) (v : CVector ι) :
    realQuadratic M v =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M).reApplyInnerSelf v := by
  exact inner_re_symm (𝕜 := ℂ) v
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M v)

lemma realQuadratic_eq_linear (M : CMatrix ι) (v : CVector ι) :
    realQuadratic M v = (inner ℂ (M.toEuclideanLin v) v).re := by
  rw [realQuadratic_eq_reApply]
  rfl

lemma realQuadratic_continuous (M : CMatrix ι) : Continuous (realQuadratic M) := by
  simpa only [realQuadratic_eq_reApply] using
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M).reApplyInnerSelf_continuous

@[simp] lemma realQuadratic_zero_vector (M : CMatrix ι) :
    realQuadratic M 0 = 0 := by
  simp [realQuadratic]

@[simp] lemma realQuadratic_zero (v : CVector ι) :
    realQuadratic (0 : CMatrix ι) v = 0 := by
  simp [realQuadratic]

lemma realQuadratic_add (M N : CMatrix ι) (v : CVector ι) :
    realQuadratic (M + N) v = realQuadratic M v + realQuadratic N v := by
  simp [realQuadratic, inner_add_right]

lemma realQuadratic_neg (M : CMatrix ι) (v : CVector ι) :
    realQuadratic (-M) v = -realQuadratic M v := by
  simp [realQuadratic]

lemma realQuadratic_sub (M N : CMatrix ι) (v : CVector ι) :
    realQuadratic (M - N) v = realQuadratic M v - realQuadratic N v := by
  simp [realQuadratic, inner_sub_right]

lemma realQuadratic_smul_matrix (c : ℝ) (M : CMatrix ι) (v : CVector ι) :
    realQuadratic ((c : ℂ) • M) v = c * realQuadratic M v := by
  simp [realQuadratic, inner_smul_right, Complex.mul_re]

lemma realQuadratic_one (v : CVector ι) :
    realQuadratic (1 : CMatrix ι) v = ‖v‖ ^ 2 := by
  simpa [realQuadratic] using (inner_self_eq_norm_sq (𝕜 := ℂ) v)

lemma realQuadratic_smul_vector (c : ℂ) (M : CMatrix ι) (v : CVector ι) :
    realQuadratic M (c • v) = ‖c‖ ^ 2 * realQuadratic M v := by
  simpa only [realQuadratic_eq_reApply] using
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M).reApplyInnerSelf_smul v (c := c)

lemma abs_realQuadratic_le (M : CMatrix ι) (v : CVector ι) :
    |realQuadratic M v| ≤ spectralNorm M * ‖v‖ ^ 2 := by
  calc
    |realQuadratic M v| ≤
        ‖inner ℂ v (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M v)‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖v‖ * ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M v‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (spectralNorm M * ‖v‖) :=
      mul_le_mul_of_nonneg_left
        ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M).le_opNorm v) (norm_nonneg v)
    _ = spectralNorm M * ‖v‖ ^ 2 := by ring

lemma realQuadratic_le_spectralNorm (M : CMatrix ι) (v : CVector ι) :
    realQuadratic M v ≤ spectralNorm M * ‖v‖ ^ 2 :=
  (le_abs_self _).trans (abs_realQuadratic_le M v)

lemma positive_quadratic_iff (M : CMatrix ι) :
    M.PosSemidef ↔ M.IsHermitian ∧ ∀ v : CVector ι, 0 ≤ realQuadratic M v := by
  rw [← Matrix.isPositive_toEuclideanLin_iff, LinearMap.IsPositive,
    Matrix.isSymmetric_toEuclideanLin_iff]
  simp only [realQuadratic_eq_linear]

lemma hermitian_real_smul (M : CMatrix ι) (hM : M.IsHermitian) (c : ℝ) :
    ((c : ℂ) • M).IsHermitian := by
  apply hM.smul
  simp [IsSelfAdjoint]

lemma realQuadratic_shift (M : CMatrix ι) (c : ℝ) (v : CVector ι) :
    realQuadratic ((c : ℂ) • (1 : CMatrix ι) + M) v =
      c * ‖v‖ ^ 2 + realQuadratic M v := by
  rw [realQuadratic_add, realQuadratic_smul_matrix, realQuadratic_one]

lemma exists_unit_same_rayleigh (M : CMatrix ι) (v : CVector ι) (hv : v ≠ 0) :
    ∃ u : CVector ι, ‖u‖ = 1 ∧
      realQuadratic M u = realQuadratic M v / ‖v‖ ^ 2 := by
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M
  have hmem : T.rayleighQuotient v ∈ T.rayleighQuotient '' ({0}ᶜ : Set (CVector ι)) :=
    ⟨v, by simpa using hv, rfl⟩
  rw [T.image_rayleigh_eq_image_rayleigh_sphere (by norm_num : (0 : ℝ) < 1)] at hmem
  obtain ⟨u, hu, he⟩ := hmem
  have hu1 : ‖u‖ = 1 := by simpa using hu
  refine ⟨u, hu1, ?_⟩
  simpa only [ContinuousLinearMap.rayleighQuotient, T,
    ← realQuadratic_eq_reApply, hu1, one_pow, div_one] using he

end FiniteCoordinates

theorem pencil_isHermitian {n : ℕ} (X T : Square n) (hT : T.IsHermitian) :
    (pencil X T).IsHermitian := by
  exact hT.fromBlocks rfl hT.neg

#print axioms positive_quadratic_iff
#assert_trust kernel positive_quadratic_iff
#print axioms pencil_isHermitian
#assert_trust kernel pencil_isHermitian

end NLA.MI04
