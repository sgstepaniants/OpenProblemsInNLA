/-
NR-03 modular bounded development draft.

This file is a mechanically separated portion of the source candidate at
commit d8b65ab13ee9c27e8909052de792f10322a51e1b. It preserves the approved
Definitions/Challenge boundary. This scratch package is not a verification
claim; authoritative LeanCert, Comparator, kernel and sandbox checks remain
pending.
-/
import NLA.NR03.Index
import NLA.NR03.FamilyIdentities
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
open scoped BigOperators Matrix
noncomputable section

namespace NLA.NR03

theorem full_identity (a b : Mask7) :
    fullSum a b = sourceD b * natTarget a b := by
  calc
    fullSum a b = coreSum a b + singletonSum a b + pairSum a b + fourSum a b := by
      change (∑ k : AtomIndex, sourceW a k * sourceV k b) = _
      rw [fin127_sum_split]
      simp_rw [sourceW_core, sourceV_core, sourceW_singleton, sourceV_singleton,
        sourceW_pair, sourceV_pair, sourceW_four, sourceV_four]
    _ = coreClosed a b + singletonClosed a b + pairClosed a b + fourClosed a b := by
      rw [core_identity, singleton_identity a b, pair_identity a b, four_identity a b]
    _ = sourceD b * natTarget a b := closed_family_identity a b

/- The actual matrices consumed by HasScaledIntegerCertificate are indexed by
   all Boolean vectors.  Their entries are the generic family definitions,
   so the preceding mask identity is their exact kernel proof. -/
def genericW : Matrix (BoolVec 7) (Fin 127) ℕ :=
  fun a k => sourceW (maskOfVector a) k

def genericV : Matrix (Fin 127) (BoolVec 7) ℕ :=
  fun k b => sourceV k (maskOfVector b)

def genericD : BoolVec 7 → ℕ :=
  fun b => sourceD (maskOfVector b)

theorem genericD_positive : ∀ b : BoolVec 7, 0 < genericD b := by
  intro b
  unfold genericD sourceD
  split
  · norm_num
  · have hp : 0 < maskCard (maskOfVector b) - 1 := by omega
    exact Nat.pow_pos hp _

theorem generic_scaled_identity (a b : BoolVec 7) :
    (castNatMatrix genericW * castNatMatrix genericV) a b =
      (genericD b : ℝ) * cMatrix 7 a b := by
  have hnat := full_identity (maskOfVector a) (maskOfVector b)
  have hcast := congrArg (fun z : ℕ => (z : ℝ)) hnat
  calc
    (castNatMatrix genericW * castNatMatrix genericV) a b =
        (fullSum (maskOfVector a) (maskOfVector b) : ℝ) := by
      simp [castNatMatrix, genericW, genericV, fullSum, Matrix.mul_apply,
        Nat.cast_sum, Nat.cast_mul]
    _ = (sourceD (maskOfVector b) : ℝ) *
          (natTarget (maskOfVector a) (maskOfVector b) : ℝ) := by
      simpa [Nat.cast_mul] using hcast
    _ = (genericD b : ℝ) * cMatrix 7 a b := by
      simp [genericD, natTarget_cast]

end NLA.NR03
