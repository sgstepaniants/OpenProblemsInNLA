/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original approximate-extremal-norm argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The norm is constructed from actual words. Its finiteness, definiteness,
triangle inequality, complex homogeneity and generator inequality are proved.
The same construction will also discharge the interspersed-product estimate.
-/
import NLA.MF07.MatrixBasics

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF07

@[simp] lemma applyMatrix_one {d : ℕ} (x : EuclideanVector d) :
    applyMatrix (1 : Square d) x = x := by
  simp [applyMatrix]

lemma applyMatrix_mul {d : ℕ} (A B : Square d) (x : EuclideanVector d) :
    applyMatrix (A * B) x = applyMatrix A (applyMatrix B x) := by
  simp [applyMatrix, map_mul]

lemma applyMatrix_add {d : ℕ} (A B : Square d) (x : EuclideanVector d) :
    applyMatrix (A + B) x = applyMatrix A x + applyMatrix B x := by
  simp [applyMatrix, map_add]

lemma applyMatrix_add_vector {d : ℕ} (A : Square d) (x y : EuclideanVector d) :
    applyMatrix A (x+y) = applyMatrix A x + applyMatrix A y := by
  exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A).map_add x y

lemma applyMatrix_smul_vector {d : ℕ} (A : Square d) (c : ℂ) (x : EuclideanVector d) :
    applyMatrix A (c • x) = c • applyMatrix A x := by
  exact (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A).map_smul c x

lemma norm_applyMatrix_le {d : ℕ} (A : Square d) (x : EuclideanVector d) :
    ‖applyMatrix A x‖ ≤ spectralNorm A * ‖x‖ :=
  (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) A).le_opNorm x

/-- All nonnegative discounted orbit values, with the empty word included. -/
def envelopeValues {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u : ℝ) (x : EuclideanVector d) : Set ℝ :=
  {r | ∃ z : List (Square d), WordIn M z ∧
    r = (u ^ z.length)⁻¹ * ‖applyMatrix (matrixProduct (z.map C)) x‖}

def productEnvelope {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u : ℝ) (x : EuclideanVector d) : ℝ := sSup (envelopeValues M C u x)

lemma envelopeValues_empty {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u : ℝ) (x : EuclideanVector d) : ‖x‖ ∈ envelopeValues M C u x := by
  refine ⟨[], WordIn_nil M, ?_⟩
  simp

lemma envelopeValues_bddAbove {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (x : EuclideanVector d) :
    ∀ r ∈ envelopeValues M C u x, r ≤ K * ‖x‖ := by
  rintro r ⟨z, hz, rfl⟩
  have hp : 0 < u ^ z.length := pow_pos hu _
  have ha := norm_applyMatrix_le (matrixProduct (z.map C)) x
  have hb := mul_le_mul_of_nonneg_right (hC z hz) (norm_nonneg x)
  have hc := mul_le_mul_of_nonneg_left (ha.trans hb) (inv_nonneg.mpr hp.le)
  calc
    (u ^ z.length)⁻¹ * ‖applyMatrix (matrixProduct (z.map C)) x‖ ≤
        (u ^ z.length)⁻¹ * (K * u ^ z.length * ‖x‖) := hc
    _ = K * ‖x‖ := by field_simp

lemma productEnvelope_bounds {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (x : EuclideanVector d) :
    ‖x‖ ≤ productEnvelope M C u x ∧ productEnvelope M C u x ≤ K * ‖x‖ := by
  have hb := envelopeValues_bddAbove M C u K hu hC x
  exact ⟨le_csSup ⟨K * ‖x‖, hb⟩ (envelopeValues_empty M C u x),
    csSup_le ⟨‖x‖, envelopeValues_empty M C u x⟩ hb⟩

lemma envelope_word_le {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (x : EuclideanVector d) (z : List (Square d)) (hz : WordIn M z) :
    (u ^ z.length)⁻¹ * ‖applyMatrix (matrixProduct (z.map C)) x‖ ≤
      productEnvelope M C u x := by
  exact le_csSup ⟨K * ‖x‖, envelopeValues_bddAbove M C u K hu hC x⟩ ⟨z, hz, rfl⟩

lemma productEnvelope_triangle {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (x y : EuclideanVector d) :
    productEnvelope M C u (x+y) ≤ productEnvelope M C u x + productEnvelope M C u y := by
  apply csSup_le ⟨‖x+y‖, envelopeValues_empty M C u (x+y)⟩
  rintro r ⟨z, hz, rfl⟩
  rw [applyMatrix_add_vector]
  calc
    (u ^ z.length)⁻¹ * ‖applyMatrix (matrixProduct (z.map C)) x +
        applyMatrix (matrixProduct (z.map C)) y‖ ≤
        (u ^ z.length)⁻¹ * (‖applyMatrix (matrixProduct (z.map C)) x‖ +
          ‖applyMatrix (matrixProduct (z.map C)) y‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ ≤ productEnvelope M C u x + productEnvelope M C u y := by
      rw [mul_add]
      exact add_le_add (envelope_word_le M C u K hu hC x z hz)
        (envelope_word_le M C u K hu hC y z hz)

lemma productEnvelope_smul_le {d : ℕ} (M : Set (Square d)) (C : Square d → Square d)
    (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (c : ℂ) (x : EuclideanVector d) :
    productEnvelope M C u (c • x) ≤ ‖c‖ * productEnvelope M C u x := by
  apply csSup_le ⟨‖c • x‖, envelopeValues_empty M C u (c • x)⟩
  rintro r ⟨z, hz, rfl⟩
  rw [applyMatrix_smul_vector, norm_smul]
  calc
    (u ^ z.length)⁻¹ * (‖c‖ * ‖applyMatrix (matrixProduct (z.map C)) x‖) =
        ‖c‖ * ((u ^ z.length)⁻¹ * ‖applyMatrix (matrixProduct (z.map C)) x‖) := by ring
    _ ≤ ‖c‖ * productEnvelope M C u x :=
      mul_le_mul_of_nonneg_left (envelope_word_le M C u K hu hC x z hz) (norm_nonneg c)

lemma productEnvelope_isComplexNorm {d : ℕ} (M : Set (Square d))
    (C : Square d → Square d) (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length) :
    IsComplexNorm (productEnvelope M C u) := by
  have hb := productEnvelope_bounds M C u K hu hC
  have hnonneg : ∀ x, 0 ≤ productEnvelope M C u x := fun x => (norm_nonneg x).trans (hb x).1
  have hz : productEnvelope M C u 0 = 0 := by
    exact le_antisymm (by simpa using (hb 0).2) (hnonneg 0)
  refine ⟨hnonneg, ?_, productEnvelope_triangle M C u K hu hC, ?_⟩
  · intro x
    constructor
    · intro hx
      have hnx : ‖x‖ ≤ 0 := by simpa [hx] using (hb x).1
      exact norm_eq_zero.mp (le_antisymm hnx (norm_nonneg x))
    · rintro rfl
      exact hz
  · intro c x
    apply le_antisymm (productEnvelope_smul_le M C u K hu hC c x)
    by_cases hc : c = 0
    · simp [hc, hz]
    · have hback := productEnvelope_smul_le M C u K hu hC c⁻¹ (c • x)
      rw [inv_smul_smul₀ hc] at hback
      have hmul := mul_le_mul_of_nonneg_left hback (norm_nonneg c)
      simpa [norm_inv, mul_assoc, norm_ne_zero_iff.mpr hc] using hmul

lemma productEnvelope_generator {d : ℕ} (M : Set (Square d))
    (C : Square d → Square d) (u K : ℝ) (hu : 0 < u)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (A : Square d) (hA : A ∈ M) (x : EuclideanVector d) :
    productEnvelope M C u (applyMatrix (C A) x) ≤ u * productEnvelope M C u x := by
  apply csSup_le ⟨_, envelopeValues_empty M C u _⟩
  rintro r ⟨z, hz, rfl⟩
  have hword : WordIn M (A :: z) := (WordIn_cons_iff M A z).mpr ⟨hA, hz⟩
  have hw := envelope_word_le M C u K hu hC x (A :: z) hword
  have hp : u ^ z.length ≠ 0 := pow_ne_zero _ hu.ne'
  have he : (u ^ z.length)⁻¹ *
        ‖applyMatrix (matrixProduct (z.map C)) (applyMatrix (C A) x)‖ =
      u * ((u ^ (A :: z).length)⁻¹ *
        ‖applyMatrix (matrixProduct ((A :: z).map C)) x‖) := by
    simp only [List.map_cons, matrixProduct_cons, applyMatrix_mul, List.length_cons, pow_succ]
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_left hw hu.le

#print axioms productEnvelope_isComplexNorm
#assert_trust kernel productEnvelope_isComplexNorm
#print axioms productEnvelope_generator
#assert_trust kernel productEnvelope_generator

end NLA.MF07
