/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematics: Matthew J. Colbrook, University of Cambridge DAMTP.

The exact two-sided Rayleigh bounds have the same right-hand limit.
No eigenvector perturbation, numerical root or interval computation is needed.
-/
import NLA.MI04.UpperBound
import Mathlib.Topology.Order.Basic

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
open scoped BigOperators Topology ComplexOrder
open Filter

namespace NLA.MI04
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma upperCoefficient_tendsto (d : ι → ℝ) (V : CMatrix ι) (a : ι)
    (hd : ∀ j, j ≠ a → d j ≤ (1 : ℝ) / 2) :
    Tendsto (upperCoefficient d V a) (𝓝[>] (0 : ℝ))
      (𝓝 (secondCoefficient d V a)) := by
  have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  unfold upperCoefficient secondCoefficient
  apply tendsto_finsetSum
  intro j _
  by_cases hj : j = a
  · simp only [if_pos hj]
    exact tendsto_const_nhds
  · simp only [if_neg hj]
    have hgap : 1 - d j ≠ 0 := by
      have h := hd j hj
      linarith
    have hden : Tendsto (fun ε : ℝ => 1 - d j - ε * spectralNorm V)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 - d j)) := by
      simpa only [zero_mul, sub_zero] using
        tendsto_const_nhds.sub (ht.mul_const (spectralNorm V))
    exact tendsto_const_nhds.div hden hgap

lemma lowerCoefficient_tendsto (d : ι → ℝ) (V : CMatrix ι) (a : ι) :
    Tendsto (fun ε : ℝ =>
      (secondCoefficient d V a + ε * realQuadratic V (correctionVector d V a)) /
        (1 + ε ^ 2 * ‖correctionVector d V a‖ ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (secondCoefficient d V a)) := by
  have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hnum : Tendsto (fun ε : ℝ =>
      secondCoefficient d V a + ε * realQuadratic V (correctionVector d V a))
      (𝓝[>] (0 : ℝ)) (𝓝 (secondCoefficient d V a)) := by
    simpa only [zero_mul, add_zero] using
      tendsto_const_nhds.add (ht.mul_const (realQuadratic V (correctionVector d V a)))
  have hden : Tendsto (fun ε : ℝ => 1 + ε ^ 2 * ‖correctionVector d V a‖ ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero] using
      tendsto_const_nhds.add ((ht.pow 2).mul_const (‖correctionVector d V a‖ ^ 2))
  simpa only [Pi.div_def, div_one] using hnum.div hden (one_ne_zero : (1 : ℝ) ≠ 0)

variable [Nonempty ι]

theorem simple_peak_second_order (d : ι → ℝ) (V : CMatrix ι) (a : ι)
    (ha : d a = 1) (hd : ∀ j, j ≠ a → d j ≤ (1 : ℝ) / 2)
    (hV : V.IsHermitian) (haa : V a a = 0) :
    Tendsto (fun ε : ℝ => (topValue (perturbedDiagonal d V ε) - 1) / ε ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (secondCoefficient d V a)) := by
  have ht : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ε * (1 + spectralNorm V) < (1 : ℝ) / 4 := by
    apply (ht.mul_const (1 + spectralNorm V)).eventually_lt_const
    norm_num
  have hpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
    eventually_mem_nhdsWithin
  have hsandwich : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      (secondCoefficient d V a + ε * realQuadratic V (correctionVector d V a)) /
          (1 + ε ^ 2 * ‖correctionVector d V a‖ ^ 2) ≤
        (topValue (perturbedDiagonal d V ε) - 1) / ε ^ 2 ∧
      (topValue (perturbedDiagonal d V ε) - 1) / ε ^ 2 ≤
        upperCoefficient d V a ε := by
    filter_upwards [hpos, hsmall] with ε hε hs
    exact simple_peak_sandwich d V a ha hd hV haa ε hε hs
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (lowerCoefficient_tendsto d V a) (upperCoefficient_tendsto d V a hd)
    (hsandwich.mono fun _ h => h.1) (hsandwich.mono fun _ h => h.2)

#print axioms simple_peak_second_order
#assert_trust kernel simple_peak_second_order

end NLA.MI04
