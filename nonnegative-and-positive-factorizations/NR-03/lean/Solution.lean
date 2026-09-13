/-
Proof candidate for the NR-03 counterexample.

The four atom families are the complementary-pair, singleton, pair and
four-set families in Sidney Holden's construction.  The retained JSON is
source data only; the candidate proves the exact identity from the family
definitions in Lean.  No untrusted native evaluation, placeholder theorem,
imported Challenge theorem, or unproved certificate-correctness premise is used.
Authoritative elaboration and independent final review are still pending.
-/
import NLA.NR03.Definitions
import Init.Data.Nat.Bitwise.Lemmas
import LeanCert.Tactic.Verification
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000
set_option leancert.trust "kernel"
open scoped BigOperators Matrix
noncomputable section

namespace NLA.NR03

abbrev Mask7 := Fin 128

def natBool (b : Bool) : ℕ := if b = true then 1 else 0

/- Encode the coordinates recursively from the least significant bit.  The
   recursive presentation avoids enumerating all 2^7 Boolean functions in
   the kernel proof of the mask/vector correspondence. -/
def encodeNat : (n : ℕ) → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n + 1, a =>
      2 ^ n * natBool (a (Fin.last n)) +
        encodeNat n (fun i => a i.castSucc)

theorem encodeNat_lt_pow : ∀ (n : ℕ) (a : Fin n → Bool),
    encodeNat n a < 2 ^ n := by
  intro n
  induction n with
  | zero =>
      intro a
      simp [encodeNat]
  | succ n ih =>
      intro a
      have ht := ih (fun i => a i.castSucc)
      cases h : a (Fin.last n) <;>
        simp [encodeNat, natBool, h, Nat.pow_succ] at * <;> omega

def maskOfVector (a : BoolVec 7) : Mask7 :=
  ⟨encodeNat 7 a, by
    have h := encodeNat_lt_pow 7 a
    norm_num at h ⊢
    exact h⟩

def maskBit (m : Mask7) (i : Fin 7) : Bool :=
  decide (((m.val / (2 ^ i.val)) % 2) = 1)

def maskVector (m : Mask7) : BoolVec 7 := fun i => maskBit m i

def maskDot (m n : Mask7) : ℕ :=
  ∑ i : Fin 7, natBool (maskVector m i) * natBool (maskVector n i)

def maskCard (m : Mask7) : ℕ :=
  ∑ i : Fin 7, natBool (maskVector m i)

def natSquareOneMinus (t : ℕ) : ℕ :=
  if t ≤ 1 then (1 - t) ^ 2 else (t - 1) ^ 2

def natTarget (m n : Mask7) : ℕ := natSquareOneMinus (maskDot m n)

def maskComplement (m : Mask7) : Mask7 :=
  ⟨127 - m.val, by omega⟩

def coreMask (k : Fin 64) : Mask7 :=
  ⟨k.val, by omega⟩

def singletonMask (i : Fin 7) : Mask7 :=
  ⟨(2 ^ i.val) % 128, Nat.mod_lt _ (by decide)⟩

def pairMasks : Array Nat :=
  #[3, 5, 9, 17, 33, 65, 6, 10, 18, 34, 66, 12, 20, 36, 68, 24, 40, 72,
    48, 80, 96]

def fourMasks : Array Nat :=
  #[15, 23, 39, 71, 27, 43, 75, 51, 83, 99, 29, 45, 77, 53, 85, 101,
    57, 89, 105, 113, 30, 46, 78, 54, 86, 102, 58, 90, 106, 114, 60, 92,
    108, 116, 120]

def pairMask (k : Fin 21) : Mask7 :=
  ⟨pairMasks[k.val]! % 128, Nat.mod_lt _ (by decide)⟩

def fourMask (k : Fin 35) : Mask7 :=
  ⟨fourMasks[k.val]! % 128, Nat.mod_lt _ (by decide)⟩

def maskSubset (s a : Mask7) : Prop :=
  ∀ i : Fin 7, maskVector s i = true → maskVector a i = true

instance : DecidableRel maskSubset := by
  intro s a
  unfold maskSubset
  infer_instance

def hFour (t : ℕ) : ℕ := t - 2

abbrev AtomIndex := Fin (64 + 7 + 21 + 35)

def coreIndex (k : Fin 64) : AtomIndex :=
  Fin.castAdd 35 (Fin.castAdd 21 (Fin.castAdd 7 k))

def singletonIndex (k : Fin 7) : AtomIndex :=
  Fin.castAdd 35 (Fin.castAdd 21 (Fin.natAdd 64 k))

def pairIndex (k : Fin 21) : AtomIndex :=
  Fin.castAdd 35 (Fin.natAdd (64 + 7) k)

def fourIndex (k : Fin 35) : AtomIndex :=
  Fin.natAdd (64 + 7 + 21) k

def coreW (a : Mask7) (k : Fin 64) : ℕ :=
  if a = coreMask k ∨ a = maskComplement (coreMask k) then 1 else 0

def coreV (k : Fin 64) (b : Mask7) : ℕ :=
  natSquareOneMinus (maskDot (coreMask k) b) *
    natSquareOneMinus (maskDot (maskComplement (coreMask k)) b)

def singletonW (a : Mask7) (i : Fin 7) : ℕ :=
  if maskBit a i = false then 1 else 0

def singletonV (i : Fin 7) (b : Mask7) : ℕ :=
  if b = singletonMask i then 1 else 0

def pairW (a : Mask7) (k : Fin 21) : ℕ :=
  if maskSubset (pairMask k) a then 1 else 0

def pairV (k : Fin 21) (b : Mask7) : ℕ :=
  if maskSubset (pairMask k) b then 4 * (maskCard b - 2) else 0

def fourW (a : Mask7) (k : Fin 35) : ℕ :=
  hFour (maskDot (fourMask k) a)

def fourV (k : Fin 35) (b : Mask7) : ℕ :=
  if maskSubset (fourMask k) b then 12 else 0

def sourceW (a : Mask7) (k : AtomIndex) : ℕ :=
  if hk : k.val < 64 then
    coreW a ⟨k.val, hk⟩
  else if hk : k.val < 71 then
    singletonW a ⟨k.val - 64, by omega⟩
  else if hk : k.val < 92 then
    pairW a ⟨k.val - 71, by omega⟩
  else
    fourW a ⟨k.val - 92, by omega⟩

def sourceV (k : AtomIndex) (b : Mask7) : ℕ :=
  if hk : k.val < 64 then
    coreV ⟨k.val, hk⟩ b
  else if hk : k.val < 71 then
    singletonV ⟨k.val - 64, by omega⟩ b
  else if hk : k.val < 92 then
    pairV ⟨k.val - 71, by omega⟩ b
  else
    fourV ⟨k.val - 92, by omega⟩ b

def sourceD (b : Mask7) : ℕ :=
  if maskCard b ≤ 1 then 1 else (maskCard b - 1) ^ 2

def coreSum (a b : Mask7) : ℕ :=
  ∑ k : Fin 64, coreW a k * coreV k b

def singletonSum (a b : Mask7) : ℕ :=
  ∑ k : Fin 7, singletonW a k * singletonV k b

def pairSum (a b : Mask7) : ℕ :=
  ∑ k : Fin 21, pairW a k * pairV k b

def fourSum (a b : Mask7) : ℕ :=
  ∑ k : Fin 35, fourW a k * fourV k b

def fullSum (a b : Mask7) : ℕ :=
  ∑ k : AtomIndex, sourceW a k * sourceV k b

def coreClosed (a b : Mask7) : ℕ :=
  natSquareOneMinus (maskDot a b) *
    natSquareOneMinus (maskCard b - maskDot a b)

def singletonClosed (a b : Mask7) : ℕ :=
  if maskCard b = 1 then 1 - maskDot a b else 0

def pairClosed (a b : Mask7) : ℕ :=
  4 * (maskCard b - 2) * Nat.choose (maskDot a b) 2

def fourClosed (a b : Mask7) : ℕ :=
  12 * ((maskCard b - maskDot a b) * Nat.choose (maskDot a b) 3 +
    2 * Nat.choose (maskDot a b) 4)

/- The all-Boolean-vector to mask correspondence is proved before the
   certificate is consumed.  This is intentionally a structural kernel
   proof, not a Python-side indexing assumption or a 128^2 finite table. -/
theorem encodeNat_testBit : ∀ (n : ℕ) (a : Fin n → Bool) (i : Fin n),
    Nat.testBit (encodeNat n a) i.val = a i := by
  intro n
  induction n with
  | zero =>
      intro a i
      exact Fin.elim0 i
  | succ n ih =>
      intro a i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change Nat.testBit (encodeNat (n + 1) a) n = a (Fin.last n)
        have ht := encodeNat_lt_pow n (fun j => a j.castSucc)
        rw [show encodeNat (n + 1) a =
          2 ^ n * natBool (a (Fin.last n)) +
            encodeNat n (fun j => a j.castSucc) by rfl]
        rw [Nat.testBit_two_pow_mul_add
          (natBool (a (Fin.last n))) ht n]
        cases h : a (Fin.last n) <;> simp [natBool, h]
      · change Nat.testBit (encodeNat (n + 1) a) j.val = a j.castSucc
        have ht := encodeNat_lt_pow n (fun j => a j.castSucc)
        rw [show encodeNat (n + 1) a =
          2 ^ n * natBool (a (Fin.last n)) +
            encodeNat n (fun j => a j.castSucc) by rfl]
        rw [Nat.testBit_two_pow_mul_add
          (natBool (a (Fin.last n))) ht j.val]
        simp [j.isLt, ih]

theorem maskVector_maskOfVector (a : BoolVec 7) :
    maskVector (maskOfVector a) = a := by
  funext i
  change decide (((encodeNat 7 a / (2 ^ i.val)) % 2) = 1) = a i
  rw [← Nat.testBit_eq_decide_div_mod_eq]
  exact encodeNat_testBit 7 a i

theorem maskDot_maskOfVector (a b : BoolVec 7) :
    maskDot (maskOfVector a) (maskOfVector b) =
      ∑ i : Fin 7, natBool (a i) * natBool (b i) := by
  simp [maskDot, maskVector_maskOfVector]

theorem maskCard_maskOfVector (a : BoolVec 7) :
    maskCard (maskOfVector a) = ∑ i : Fin 7, natBool (a i) := by
  simp [maskCard, maskVector_maskOfVector]

theorem natBool_cast (b : Bool) :
    (natBool b : ℝ) = boolToReal b := by
  cases b <;> simp [natBool, boolToReal]

theorem natSquareOneMinus_cast (t : ℕ) :
    (natSquareOneMinus t : ℝ) = (1 - (t : ℝ)) ^ 2 := by
  by_cases ht : t ≤ 1
  · simp [natSquareOneMinus, ht, Nat.cast_sub ht]
  · have ht' : 1 ≤ t := by omega
    simp [natSquareOneMinus, ht, Nat.cast_sub ht']
    ring

theorem natTarget_cast (a b : BoolVec 7) :
    (natTarget (maskOfVector a) (maskOfVector b) : ℝ) =
      cMatrix 7 a b := by
  rw [natTarget, natSquareOneMinus_cast, maskDot_maskOfVector]
  simp only [cMatrix, boolDot, Nat.cast_sum, Nat.cast_mul, natBool_cast]

/- The abstract sum splitter keeps the finite family decomposition cheap: it
   is proved once for an arbitrary summand, without unfolding any certificate
   data. -/
theorem fin127_sum_split (f : AtomIndex → ℕ) :
    (∑ k : AtomIndex, f k) =
      (∑ k : Fin 64, f (coreIndex k)) +
        (∑ k : Fin 7, f (singletonIndex k)) +
        (∑ k : Fin 21, f (pairIndex k)) +
        (∑ k : Fin 35, f (fourIndex k)) := by
  have houter := Fin.sum_univ_add f
  have hmid := Fin.sum_univ_add
    (fun k : Fin (64 + 7 + 21) => f (Fin.castAdd 35 k))
  have hinner := Fin.sum_univ_add
    (fun k : Fin (64 + 7) => f (Fin.castAdd 35 (Fin.castAdd 21 k)))
  rw [houter, hmid, hinner]

theorem sourceW_core (a : Mask7) (k : Fin 64) :
    sourceW a (coreIndex k) = coreW a k := by
  simp [sourceW, coreIndex, k.isLt]

theorem sourceV_core (k : Fin 64) (b : Mask7) :
    sourceV (coreIndex k) b = coreV k b := by
  simp [sourceV, coreIndex, k.isLt]

theorem sourceW_singleton (a : Mask7) (k : Fin 7) :
    sourceW a (singletonIndex k) = singletonW a k := by
  have hk : k.val < 7 := k.isLt
  have h64 : ¬ (64 + k.val < 64) := by omega
  have h71 : 64 + k.val < 71 := by omega
  simp [sourceW, singletonIndex, h64, h71]

theorem sourceV_singleton (k : Fin 7) (b : Mask7) :
    sourceV (singletonIndex k) b = singletonV k b := by
  have hk : k.val < 7 := k.isLt
  have h64 : ¬ (64 + k.val < 64) := by omega
  have h71 : 64 + k.val < 71 := by omega
  simp [sourceV, singletonIndex, h64, h71]

theorem sourceW_pair (a : Mask7) (k : Fin 21) :
    sourceW a (pairIndex k) = pairW a k := by
  have hk : k.val < 21 := k.isLt
  have h64 : ¬ (71 + k.val < 64) := by omega
  have h71 : ¬ (71 + k.val < 71) := by omega
  have h92 : 71 + k.val < 92 := by omega
  simp [sourceW, pairIndex, h64, h71, h92]

theorem sourceV_pair (k : Fin 21) (b : Mask7) :
    sourceV (pairIndex k) b = pairV k b := by
  have hk : k.val < 21 := k.isLt
  have h64 : ¬ (71 + k.val < 64) := by omega
  have h71 : ¬ (71 + k.val < 71) := by omega
  have h92 : 71 + k.val < 92 := by omega
  simp [sourceV, pairIndex, h64, h71, h92]

theorem sourceW_four (a : Mask7) (k : Fin 35) :
    sourceW a (fourIndex k) = fourW a k := by
  have hk : k.val < 35 := k.isLt
  have h64 : ¬ (92 + k.val < 64) := by omega
  have h71 : ¬ (92 + k.val < 71) := by omega
  have h92 : ¬ (92 + k.val < 92) := by omega
  simp [sourceW, fourIndex, h64, h71, h92]

theorem sourceV_four (k : Fin 35) (b : Mask7) :
    sourceV (fourIndex k) b = fourV k b := by
  have hk : k.val < 35 := k.isLt
  have h64 : ¬ (92 + k.val < 64) := by omega
  have h71 : ¬ (92 + k.val < 71) := by omega
  have h92 : ¬ (92 + k.val < 92) := by omega
  simp [sourceV, fourIndex, h64, h71, h92]

def coreRep (a : Mask7) : Fin 64 :=
  if h : a.val < 64 then ⟨a.val, h⟩ else ⟨127 - a.val, by omega⟩

/- This is only a 128-by-64 Boolean/index check; it replaces a 64-term
   symbolic sum by its unique nonzero complementary-pair summand. -/
theorem coreW_indicator (a : Mask7) (k : Fin 64) :
    coreW a k = if k = coreRep a then 1 else 0 := by
  have halt : a.val < 128 := a.isLt
  have hklt : k.val < 64 := k.isLt
  by_cases ha : a.val < 64
  · have hrep : coreRep a = ⟨a.val, ha⟩ := by
      simp [coreRep, ha]
    rw [hrep]
    by_cases h : a = coreMask k
    · have hk : k = ⟨a.val, ha⟩ := by
        apply Fin.ext
        have hv := congrArg (fun z : Mask7 => z.val) h
        simpa [coreMask] using hv.symm
      have hcomp : a ≠ maskComplement (coreMask k) := by
        intro h'
        have hv := congrArg (fun z : Mask7 => z.val) h'
        simp [maskComplement, coreMask] at hv
        omega
      simp [coreW, h, hcomp, hk]
    · have hk : k ≠ ⟨a.val, ha⟩ := by
        intro hk'
        apply h
        apply Fin.ext
        have hv := congrArg (fun z : Fin 64 => z.val) hk'
        simpa [coreMask] using hv.symm
      have hcomp : a ≠ maskComplement (coreMask k) := by
        intro h'
        have hv := congrArg (fun z : Mask7 => z.val) h'
        simp [maskComplement, coreMask] at hv
        omega
      simp [coreW, h, hcomp, hk]
  · have hrep : coreRep a = ⟨127 - a.val, by omega⟩ := by
      simp [coreRep, ha]
    rw [hrep]
    have hlow : a ≠ coreMask k := by
      intro h'
      have hv := congrArg (fun z : Mask7 => z.val) h'
      simp [coreMask] at hv
      omega
    by_cases h : a = maskComplement (coreMask k)
    · have hk : k = ⟨127 - a.val, by omega⟩ := by
        apply Fin.ext
        have hv := congrArg (fun z : Mask7 => z.val) h
        simp [maskComplement, coreMask] at hv
        omega
      simp [coreW, h, hlow, hk]
    · have hk : k ≠ ⟨127 - a.val, by omega⟩ := by
        intro hk'
        apply h
        apply Fin.ext
        have hv := congrArg (fun z : Fin 64 => z.val) hk'
        simp [maskComplement, coreMask] at hv
        omega
      simp [coreW, h, hlow, hk]

theorem coreV_at_rep (a b : Mask7) :
    coreV (coreRep a) b = coreClosed a b := by
  have h : ∀ a b : Mask7,
      coreV (coreRep a) b = coreClosed a b := by
    intro a
    fin_cases a <;> decide
  exact h a b

theorem core_identity (a b : Mask7) :
    coreSum a b = coreClosed a b := by
  change (∑ k : Fin 64, coreW a k * coreV k b) = coreClosed a b
  calc
    (∑ k : Fin 64, coreW a k * coreV k b) =
        ∑ k : Fin 64, (if k = coreRep a then 1 else 0) * coreV k b := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [coreW_indicator]
    _ = coreV (coreRep a) b := by simp
    _ = coreClosed a b := coreV_at_rep a b

/- Each remaining source family is explicitly finite.  The singleton, pair,
   and four-set identities inspect only 7, 21, or 35 summands per row-local
   check; the closed-family identity below is reduced further to its two
   cardinality parameters.  The large 128-by-127 matrix multiplication is
   never unfolded. -/
theorem singleton_identity : ∀ a b : Mask7,
    singletonSum a b = singletonClosed a b := by
  intro a
  fin_cases a <;> decide

theorem pair_identity : ∀ a b : Mask7,
    pairSum a b = pairClosed a b := by
  intro a
  fin_cases a <;> decide

theorem four_identity : ∀ a b : Mask7,
    fourSum a b = fourClosed a b := by
  intro a
  fin_cases a <;> decide

theorem natBool_le_one (b : Bool) : natBool b ≤ 1 := by
  cases b <;> simp [natBool]

theorem maskCard_le_seven (b : Mask7) : maskCard b ≤ 7 := by
  unfold maskCard
  calc
    (∑ i : Fin 7, natBool (maskVector b i)) ≤ ∑ i : Fin 7, 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact natBool_le_one _
    _ = 7 := by simp

theorem maskDot_le_card (a b : Mask7) :
    maskDot a b ≤ maskCard b := by
  unfold maskDot maskCard
  apply Finset.sum_le_sum
  intro i hi
  cases ha : maskVector a i <;> cases hb : maskVector b i <;>
    simp [natBool, ha, hb]

/- The closed family calculation depends only on the two cardinality
   parameters s = |b| and t = |a ∩ b|.  It is checked over Fin 8 squared
   (with the implication t ≤ s), rather than by expanding all 128^2 mask
   pairs. -/
theorem closed_arithmetic :
    ∀ s t : Fin 8, t.val ≤ s.val →
      natSquareOneMinus t.val * natSquareOneMinus (s.val - t.val) +
          (if s.val = 1 then 1 - t.val else 0) +
          4 * (s.val - 2) * Nat.choose t.val 2 +
          12 * ((s.val - t.val) * Nat.choose t.val 3 +
            2 * Nat.choose t.val 4) =
        (if s.val ≤ 1 then 1 else (s.val - 1) ^ 2) *
          natSquareOneMinus t.val := by
  decide

theorem closed_family_identity : ∀ a b : Mask7,
    coreClosed a b + singletonClosed a b + pairClosed a b + fourClosed a b =
      sourceD b * natTarget a b := by
  intro a b
  have hs : maskCard b ≤ 7 := maskCard_le_seven b
  have ht : maskDot a b ≤ maskCard b := maskDot_le_card a b
  let s : Fin 8 := ⟨maskCard b, by omega⟩
  let t : Fin 8 := ⟨maskDot a b, by omega⟩
  have hst : t.val ≤ s.val := by
    simpa [s, t] using ht
  have h := closed_arithmetic s t hst
  simpa [coreClosed, singletonClosed, pairClosed, fourClosed,
    sourceD, natTarget, s, t] using h

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

/- General denominator bridge.  The proof explicitly distributes the common
   positive denominator through the finite matrix sum. -/
theorem scaled_certificate_gives_factorization
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (X : Matrix ι κ ℝ) (r : ℕ)
    (h : HasScaledIntegerCertificate X r) :
    ∃ W : Matrix ι (Fin r) ℕ,
      ∃ V : Matrix (Fin r) κ ℕ,
        ∃ d : κ → ℕ,
          (∀ j, 0 < d j) ∧
          (∀ i j,
            (castNatMatrix W * castNatMatrix V) i j =
              (d j : ℝ) * X i j) ∧
          FactorizationData X r (castNatMatrix W)
            (scaledRightFactor V d) := by
  rcases h with ⟨W, V, d, hd, hid⟩
  refine ⟨W, V, d, hd, hid, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i k
    exact_mod_cast (Nat.zero_le (W i k))
  · intro k j
    apply div_nonneg
    · exact_mod_cast (Nat.zero_le (V k j))
    · exact_mod_cast (Nat.zero_le (d j))
  · ext i j
    have hdj : (d j : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hd j))
    calc
      (castNatMatrix W * scaledRightFactor V d) i j =
          (castNatMatrix W * castNatMatrix V) i j / (d j : ℝ) := by
        simp only [Matrix.mul_apply, castNatMatrix, scaledRightFactor,
          div_eq_mul_inv]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = ((d j : ℝ) * X i j) / (d j : ℝ) := by rw [hid i j]
      _ = X i j := by
        apply (div_eq_iff hdj).2
        ring

theorem witness_scaled_certificate :
    HasScaledIntegerCertificate (cMatrix 7) 127 := by
  refine ⟨genericW, genericV, genericD, genericD_positive, ?_⟩
  exact generic_scaled_identity

theorem witness_factorization :
    HasNonnegativeFactorization (cMatrix 7) 127 := by
  rcases scaled_certificate_gives_factorization (cMatrix 7) 127
      witness_scaled_certificate with ⟨W, V, d, hd, hid, hfac⟩
  exact ⟨castNatMatrix W, scaledRightFactor V d, hfac⟩

theorem cMatrix_nonnegative (n : ℕ) :
    EntrywiseNonnegative (cMatrix n) := by
  intro a b
  exact sq_nonneg _

theorem boolVec_seven_card : Fintype.card (BoolVec 7) = 128 := by
  norm_num [BoolVec]

theorem nonnegative_rank_attained_minimal
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (X : Matrix ι κ ℝ)
    (hX : ∃ r : ℕ, HasNonnegativeFactorization X r) :
    HasNonnegativeFactorization X (nonnegativeRank X) ∧
      ∀ r : ℕ, HasNonnegativeFactorization X r →
        nonnegativeRank X ≤ r := by
  classical
  have hspec : HasNonnegativeFactorization X (Nat.find hX) :=
    Nat.find_spec hX
  have hmin : ∀ r : ℕ, HasNonnegativeFactorization X r →
      Nat.find hX ≤ r := fun r hr => Nat.find_min' hX hr
  simpa [nonnegativeRank, hX] using And.intro hspec hmin

theorem rank_le_of_factorization
    {ι κ : Type} [Fintype ι] [Fintype κ]
    (X : Matrix ι κ ℝ) (r : ℕ)
    (h : HasNonnegativeFactorization X r) :
    nonnegativeRank X ≤ r := by
  exact (nonnegative_rank_attained_minimal X ⟨r, h⟩).2 r h

theorem witness_rank_upper_bound :
    nonnegativeRank (cMatrix 7) ≤ 127 := by
  exact rank_le_of_factorization (cMatrix 7) 127 witness_factorization

theorem witness_not_full_rank :
    nonnegativeRank (cMatrix 7) < 2 ^ 7 := by
  have h := witness_rank_upper_bound
  norm_num at h ⊢
  omega

theorem not_targetStatement : ¬ targetStatement := by
  intro h
  have h7 := h 7 (by norm_num)
  have hu := witness_not_full_rank
  norm_num at h7 hu
  omega

end NLA.NR03

/- Remote harness diagnostics: each public Comparator export is checked in
   LeanCert's kernel trust mode and then printed for its transitive dependency
   boundary.  These commands are intentionally kept with the candidate so a
   successful remote run supplies the actual closure evidence. -/
#assert_trust kernel NLA.NR03.cMatrix_nonnegative
#print axioms NLA.NR03.cMatrix_nonnegative
#assert_trust kernel NLA.NR03.boolVec_seven_card
#print axioms NLA.NR03.boolVec_seven_card
#assert_trust kernel NLA.NR03.nonnegative_rank_attained_minimal
#print axioms NLA.NR03.nonnegative_rank_attained_minimal
#assert_trust kernel NLA.NR03.rank_le_of_factorization
#print axioms NLA.NR03.rank_le_of_factorization
#assert_trust kernel NLA.NR03.scaled_certificate_gives_factorization
#print axioms NLA.NR03.scaled_certificate_gives_factorization
#assert_trust kernel NLA.NR03.witness_scaled_certificate
#print axioms NLA.NR03.witness_scaled_certificate
#assert_trust kernel NLA.NR03.witness_factorization
#print axioms NLA.NR03.witness_factorization
#assert_trust kernel NLA.NR03.witness_rank_upper_bound
#print axioms NLA.NR03.witness_rank_upper_bound
#assert_trust kernel NLA.NR03.witness_not_full_rank
#print axioms NLA.NR03.witness_not_full_rank
#assert_trust kernel NLA.NR03.not_targetStatement
#print axioms NLA.NR03.not_targetStatement
