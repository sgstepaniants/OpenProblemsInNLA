/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

Unit-sphere attainment and exact variational bounds in arbitrary dimension.
-/
import NLA.MI04.Quadratic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators ComplexOrder

namespace NLA.MI04
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma topValue_attained (M : CMatrix ι) :
    ∃ u : CVector ι, ‖u‖ = 1 ∧ realQuadratic M u = topValue M ∧
      ∀ v : CVector ι, ‖v‖ = 1 → realQuadratic M v ≤ topValue M := by
  classical
  letI : ProperSpace (CVector ι) := FiniteDimensional.proper_rclike ℂ (CVector ι)
  let a : ι := Classical.choice (inferInstance : Nonempty ι)
  have hs : (Metric.sphere (0 : CVector ι) 1).Nonempty := by
    refine ⟨EuclideanSpace.basisFun ι ℂ a, ?_⟩
    simpa using (EuclideanSpace.basisFun ι ℂ).norm_eq_one a
  obtain ⟨u, hu, hmax⟩ := (isCompact_sphere (0 : CVector ι) 1).exists_isMaxOn hs
    (realQuadratic_continuous M).continuousOn
  have hu1 : ‖u‖ = 1 := by simpa using hu
  have hgreatest : IsGreatest (rayleighValues M) (realQuadratic M u) := by
    refine ⟨⟨u, hu1, rfl⟩, ?_⟩
    rintro r ⟨v, hv, rfl⟩
    exact hmax (by simpa using hv)
  have heq : topValue M = realQuadratic M u := hgreatest.csSup_eq
  refine ⟨u, hu1, heq.symm, ?_⟩
  intro v hv
  rw [heq]
  exact hmax (by simpa using hv)

theorem topValue_maximum (M : CMatrix ι) (_hM : M.IsHermitian) :
    ∃ u : CVector ι, ‖u‖ = 1 ∧ realQuadratic M u = topValue M ∧
      ∀ v : CVector ι, ‖v‖ = 1 → realQuadratic M v ≤ topValue M :=
  topValue_attained M

lemma realQuadratic_le_top_of_unit (M : CMatrix ι) (v : CVector ι) (hv : ‖v‖ = 1) :
    realQuadratic M v ≤ topValue M := by
  obtain ⟨_, _, _, h⟩ := topValue_attained M
  exact h v hv

lemma topValue_le_iff (M : CMatrix ι) (c : ℝ) :
    topValue M ≤ c ↔ ∀ v : CVector ι, ‖v‖ = 1 → realQuadratic M v ≤ c := by
  constructor
  · intro h v hv
    exact (realQuadratic_le_top_of_unit M v hv).trans h
  · intro h
    obtain ⟨u, hu, he, _⟩ := topValue_attained M
    rw [← he]
    exact h u hu

lemma realQuadratic_le_top_mul_norm_sq (M : CMatrix ι) (v : CVector ι) :
    realQuadratic M v ≤ topValue M * ‖v‖ ^ 2 := by
  by_cases hv : v = 0
  · simp [hv]
  obtain ⟨u, hu, he⟩ := exists_unit_same_rayleigh M v hv
  have h := realQuadratic_le_top_of_unit M u hu
  rw [he] at h
  exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hv))).mp h

lemma topValue_le_spectralNorm (M : CMatrix ι) : topValue M ≤ spectralNorm M := by
  apply (topValue_le_iff M _).mpr
  intro v hv
  simpa only [hv, one_pow, mul_one] using realQuadratic_le_spectralNorm M v

lemma topValue_nonneg_of_positive (M : CMatrix ι) (hM : M.PosSemidef) :
    0 ≤ topValue M := by
  obtain ⟨u, _, he, _⟩ := topValue_attained M
  rw [← he]
  exact (positive_quadratic_iff M).mp hM |>.2 u

theorem positive_norm_eq_top (M : CMatrix ι) (hM : M.PosSemidef) :
    spectralNorm M = topValue M := by
  let T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M
  have hp := (positive_quadratic_iff M).mp hM
  have hT : T.IsSymmetric := by
    change M.toEuclideanLin.IsSymmetric
    exact Matrix.isSymmetric_toEuclideanLin_iff.mpr hp.1
  apply le_antisymm ?_ (topValue_le_spectralNorm M)
  change ‖T‖ ≤ topValue M
  rw [T.norm_eq_iSup_rayleighQuotient hT]
  refine ciSup_le fun v => ?_
  have hnonneg : 0 ≤ T.rayleighQuotient v := by
    change 0 ≤ T.reApplyInnerSelf v / ‖v‖ ^ 2
    rw [← realQuadratic_eq_reApply]
    exact div_nonneg (hp.2 v) (sq_nonneg _)
  rw [abs_of_nonneg hnonneg]
  by_cases hv : v = 0
  · simpa [hv] using topValue_nonneg_of_positive M hM
  change T.reApplyInnerSelf v / ‖v‖ ^ 2 ≤ topValue M
  rw [← realQuadratic_eq_reApply]
  exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hv))).mpr
    (realQuadratic_le_top_mul_norm_sq M v)

theorem shifted_topValue (M : CMatrix ι) (_hM : M.IsHermitian) (c : ℝ) :
    topValue ((c : ℂ) • (1 : CMatrix ι) + M) = c + topValue M := by
  apply le_antisymm
  · apply (topValue_le_iff _ _).mpr
    intro v hv
    rw [realQuadratic_shift, hv, one_pow, mul_one]
    exact add_le_add_left (realQuadratic_le_top_of_unit M v hv) c
  · obtain ⟨u, hu, he, _⟩ := topValue_attained M
    have h := realQuadratic_le_top_of_unit ((c : ℂ) • (1 : CMatrix ι) + M) u hu
    simpa only [realQuadratic_shift, hu, one_pow, mul_one, he] using h

theorem scalar_order_iff_top (M : CMatrix ι) (hM : M.IsHermitian) (c : ℝ) :
    ((c : ℂ) • (1 : CMatrix ι) - M).PosSemidef ↔ topValue M ≤ c := by
  rw [positive_quadratic_iff]
  constructor
  · rintro ⟨_, h⟩
    apply (topValue_le_iff M c).mpr
    intro v hv
    have hq := h v
    rw [realQuadratic_sub, realQuadratic_smul_matrix, realQuadratic_one,
      hv, one_pow, mul_one] at hq
    exact sub_nonneg.mp hq
  · intro h
    refine ⟨(hermitian_real_smul 1 Matrix.isHermitian_one c).sub hM, ?_⟩
    intro v
    rw [realQuadratic_sub, realQuadratic_smul_matrix, realQuadratic_one]
    exact sub_nonneg.mpr ((realQuadratic_le_top_mul_norm_sq M v).trans
      (mul_le_mul_of_nonneg_right h (sq_nonneg _)))

#print axioms topValue_maximum
#assert_trust kernel topValue_maximum
#print axioms positive_norm_eq_top
#assert_trust kernel positive_norm_eq_top
#print axioms shifted_topValue
#assert_trust kernel shifted_topValue
#print axioms scalar_order_iff_top
#assert_trust kernel scalar_order_iff_top

end NLA.MI04
