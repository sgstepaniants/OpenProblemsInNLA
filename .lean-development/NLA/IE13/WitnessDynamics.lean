/-
Copyright (c) 2026 George Stepaniants.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Released under Apache 2.0 license. Substantial OpenAI Codex assistance.
Original mathematical proof: Matthew J. Colbrook, Cambridge DAMTP.

The literal rational input has the prescribed admissible physical prefix and
attains the exact recurrence entry. The full LU factors also prove nonsingularity;
no assertion about the unused prescribed suffix is needed.
-/
import NLA.IE13.WitnessProduct

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.IE13

theorem witness_prefix_admissible (p q : ℕ) (hp : 0 < p) :
    AdmissiblePrefix (witnessMatrix p q) (witnessSeedPath p q) (p + q) := by
  exact relabeled_LU_prefix_admissible
    (witnessMatrix p q) (fullLower p q) (fullUpper p q)
    (witnessFactorIndex p q) (witnessSeedPath p q) (p + q)
    (witness_factorization p q) (fullLower_triangular p q) (fullLower_diag p q)
    (fullUpper_triangular p q) (witness_seed_positions p q)
    (fun k _ => fullUpper_diag_ne_zero p q k)
    (fun k _ => witness_factor_pivot p q k)
    (fun k hk i => fullLower_prefix_norm p q k hk i)

theorem witness_target_value (p q : ℕ) (hp : 0 < p) :
    trajectory (witnessMatrix p q) (witnessSeedPath p q) (p + q)
      (witnessTarget p q) (witnessTarget p q) =
        (bandSequence p (p + q) : ℂ) := by
  have hT : p + q < witnessOrder p q := by unfold witnessOrder; omega
  have htrajectory := relabeled_LU_prefix_trajectory
    (witnessMatrix p q) (fullLower p q) (fullUpper p q)
    (witnessFactorIndex p q) (witnessSeedPath p q) (p + q)
    (witness_factorization p q) (fullLower_triangular p q) (fullLower_diag p q)
    (fullUpper_triangular p q) (witness_seed_positions p q)
    (fun k _ => fullUpper_diag_ne_zero p q k)
    (fun k _ => witness_factor_pivot p q k)
    (p + q) le_rfl hT (witnessTarget p q) (witnessTarget p q) le_rfl le_rfl
  rw [htrajectory, witness_factor_origin_after p q q (witnessTarget p q)]
  change tailEntry (fullLower p q) (fullUpper p q) (witnessTarget p q).val
    (witnessTarget p q) (witnessTarget p q) = _
  rw [tail_pivot_row (fullLower p q) (fullUpper p q)
    (fullLower_triangular p q) (fullLower_diag p q)]
  change (fullUpperRational p q (witnessTarget p q) (witnessTarget p q) : ℂ) = _
  rw [fullUpper_target]
  simp only [witnessTarget, Fin.val_mk, le_refl, ite_true,
    forwardRational, if_neg (by omega : p + q ≠ 0), Rat.cast_natCast]

theorem witness_nonsingular (p q : ℕ) (hp : 0 < p) :
    (witnessMatrix p q).det ≠ 0 := by
  apply relabeled_LU_nonsingular (witnessMatrix p q) (fullLower p q) (fullUpper p q)
    (witnessFactorEquiv p q)
  · intro i j
    exact witness_factorization p q i j
  · exact fullLower_triangular p q
  · exact fullLower_diag p q
  · exact fullUpper_triangular p q
  · exact fullUpper_diag_ne_zero p q

#print axioms witness_prefix_admissible
#assert_trust kernel witness_prefix_admissible
#print axioms witness_target_value
#assert_trust kernel witness_target_value
#print axioms witness_nonsingular
#assert_trust kernel witness_nonsingular

end NLA.IE13
