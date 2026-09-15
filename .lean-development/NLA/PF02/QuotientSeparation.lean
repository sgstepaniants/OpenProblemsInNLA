/-
Copyright (c) 2026 George Stepaniants. Apache 2.0.
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. AI-assisted implementation.
The separator is defined on the full factorization fiber and original quotient.
-/
import NLA.PF02.Algebra
import NLA.PF02.Coordinates
import NLA.PF02.Witness
import NLA.PF02.CongruenceDeterminant
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical MatrixOrder Topology
noncomputable section
namespace NLA.PF02

theorem witness_psd_rank : RealPSDRankEquals witnessMatrix 3 := by
  refine ⟨by norm_num, ⟨⟨witnessTuple, witness_factorization⟩⟩, ?_⟩
  intro r hr hF
  rcases hF with ⟨F⟩
  have hbound := factorization_rank_le_square witnessMatrix F
  rw [witness_certificates.2.2.2.2] at hbound
  by_contra hnot
  have hr2 : r ≤ 2 := by omega
  interval_cases r <;> norm_num at hbound

theorem orientation_ne_zero (F : FactorizationSpace 3 witnessMatrix) :
    orientationDeterminant (F : FactorTuple 3 6 6) ≠ 0 := by
  have hd := congrArg Matrix.det (factorization_coordinate_identity witnessMatrix F)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, witness_matrix_det] at hd
  intro hzero
  have hU : (rowCoordinateMatrix F.val.1).det = 0 := hzero
  simp only [hU, zero_mul] at hd
  norm_num at hd

theorem orientation_invariant
    (F G : FactorizationSpace 3 witnessMatrix) (h : CongruenceRel F G) :
    orientationSign F = orientationSign G := by
  rcases h with ⟨S, hS⟩
  have hd : (S : Mat 3).det ≠ 0 := (Matrix.isUnits_det_units S).ne_zero
  have hp : 0 < (S : Mat 3).det ^ 4 := by
    nlinarith [sq_pos_of_ne_zero (pow_ne_zero 2 hd)]
  have he : orientationDeterminant G.val =
      orientationDeterminant F.val * (S : Mat 3).det ^ 4 := by
    rw [hS, orientation_transform_formula, congruence_coordinate_determinant]
  simp only [orientationSign, he, mul_pos_iff_of_pos_right hp]

lemma continuous_orientationSign : Continuous orientationSign := by
  apply continuous_iff_continuousAt.2
  intro F
  by_cases hpos : 0 < orientationDeterminant F.val
  · have hN : {G : FactorizationSpace 3 witnessMatrix |
        0 < orientationDeterminant G.val} ∈ 𝓝 F :=
      (isOpen_lt continuous_const continuous_orientationDeterminant).mem_nhds hpos
    apply (continuousAt_const : ContinuousAt
      (fun _ : FactorizationSpace 3 witnessMatrix => (1 : ℝ)) F).congr
    filter_upwards [hN] with G hG
    simp [orientationSign, hG]
  · have hneg : orientationDeterminant F.val < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) (orientation_ne_zero F)
    have hN : {G : FactorizationSpace 3 witnessMatrix |
        orientationDeterminant G.val < 0} ∈ 𝓝 F :=
      (isOpen_lt continuous_orientationDeterminant continuous_const).mem_nhds hneg
    apply (continuousAt_const : ContinuousAt
      (fun _ : FactorizationSpace 3 witnessMatrix => (-1 : ℝ)) F).congr
    filter_upwards [hN] with G hG
    simp [orientationSign, not_lt.mpr (le_of_lt hG)]

theorem quotient_orientation_separation :
    ∃ ε : FactorizationOrbit 3 witnessMatrix → ℝ,
      Continuous ε ∧ Set.range ε = ({-1, 1} : Set ℝ) ∧
        ∀ F : FactorizationSpace 3 witnessMatrix,
          ε (orbitMk F) = orientationSign F := by
  let ε : FactorizationOrbit 3 witnessMatrix → ℝ :=
    Quot.lift orientationSign (fun F G h => orientation_invariant F G h)
  have hε : Continuous ε := continuous_quot_lift _ continuous_orientationSign
  have hplus : orientationSign
      (⟨witnessTuple, witness_factorization⟩ : FactorizationSpace 3 witnessMatrix) = 1 := by
    simp only [orientationSign, witness_orientations.1]
    norm_num
  have hminus : orientationSign
      (⟨reflectedTuple, reflected_factorization⟩ : FactorizationSpace 3 witnessMatrix) = -1 := by
    simp only [orientationSign, witness_orientations.2]
    norm_num
  refine ⟨ε, hε, ?_, fun _ => rfl⟩
  apply Set.ext
  intro y
  constructor
  · rintro ⟨Q, rfl⟩
    refine Quot.inductionOn Q ?_
    intro F
    change orientationSign F ∈ ({-1, 1} : Set ℝ)
    unfold orientationSign
    split_ifs <;> simp
  · intro hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with hy | hy
    · subst y
      exact ⟨orbitMk (⟨reflectedTuple, reflected_factorization⟩ :
        FactorizationSpace 3 witnessMatrix), hminus⟩
    · subst y
      exact ⟨orbitMk (⟨witnessTuple, witness_factorization⟩ :
        FactorizationSpace 3 witnessMatrix), hplus⟩

theorem witness_orbit_disconnected :
    ¬ IsConnected (Set.univ : Set (FactorizationOrbit 3 witnessMatrix)) := by
  intro hconnected
  rcases quotient_orientation_separation with ⟨ε, hε, hrange, _⟩
  have htwo : IsConnected ({-1, 1} : Set ℝ) := by
    simpa only [Set.image_univ, hrange] using hconnected.image ε hε.continuousOn
  have hz : (0 : ℝ) ∈ ({-1, 1} : Set ℝ) :=
    htwo.Icc_subset (a := (-1 : ℝ)) (b := 1) (by simp) (by simp) (by norm_num)
  norm_num at hz

theorem not_minimalPSDOrbitConnectedConjecture :
    ¬ MinimalPSDOrbitConnectedConjecture := by
  intro h
  apply witness_orbit_disconnected
  apply h 3 6 6 (by norm_num) (by norm_num) (by norm_num) witnessMatrix
  · intro i j
    exact le_of_lt (witness_certificates.1 i j)
  · simpa using witness_certificates.2.2.2.2
  · exact witness_psd_rank

#assert_trust kernel witness_psd_rank
#print axioms witness_psd_rank
#assert_trust kernel orientation_ne_zero
#print axioms orientation_ne_zero
#assert_trust kernel orientation_invariant
#print axioms orientation_invariant
#assert_trust kernel continuous_orientationSign
#print axioms continuous_orientationSign
#assert_trust kernel quotient_orientation_separation
#print axioms quotient_orientation_separation
#assert_trust kernel witness_orbit_disconnected
#print axioms witness_orbit_disconnected
#assert_trust kernel not_minimalPSDOrbitConnectedConjecture
#print axioms not_minimalPSDOrbitConnectedConjecture
end NLA.PF02
