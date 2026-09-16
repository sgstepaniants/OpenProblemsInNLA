/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Original comparison argument:
Matthew J. Colbrook, University of Cambridge, DAMTP.

The actual all-segment hypothesis constructs an equivalent orbit norm.
This proves the same interspersed estimate without enumerating 2^n summands.
The zero segment-rate case is handled separately, with the empty segment bound.
-/
import NLA.MF07.ProductEnvelope

set_option autoImplicit false
set_option leancert.trust "kernel"

noncomputable section
namespace NLA.MF07

lemma spectralNorm_eq_zero_iff {d : ℕ} (A : Square d) : spectralNorm A = 0 ↔ A = 0 := by
  constructor
  · intro h
    apply EquivLike.injective (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ))
    rw [map_zero]
    exact norm_eq_zero.mp h
  · rintro rfl
    simp [spectralNorm]

lemma norm_product_from_generator {d : ℕ} (M : Set (Square d))
    (D : Square d → Square d) (v : EuclideanVector d → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hD : ∀ A ∈ M, ∀ x, v (applyMatrix (D A) x) ≤ r * v x)
    (z : List (Square d)) (hz : WordIn M z) (x : EuclideanVector d) :
    v (applyMatrix (matrixProduct (z.map D)) x) ≤ r ^ z.length * v x := by
  induction z generalizing x with
  | nil => simp
  | cons A z ih =>
      obtain ⟨hA, hz⟩ := (WordIn_cons_iff M A z).mp hz
      simp only [List.map_cons, matrixProduct_cons, applyMatrix_mul, List.length_cons]
      calc
        v (applyMatrix (matrixProduct (z.map D)) (applyMatrix (D A) x)) ≤
            r ^ z.length * v (applyMatrix (D A) x) := ih hz _
        _ ≤ r ^ z.length * (r * v x) :=
          mul_le_mul_of_nonneg_left (hD A hA x) (pow_nonneg hr _)
        _ = r ^ (z.length+1) * v x := by rw [pow_succ]; ring

lemma interspersed_positive_rate {d : ℕ} (M : Set (Square d))
    (C E : Square d → Square d) (K u v : ℝ) (hK : 1 ≤ K)
    (hu : 0 < u) (hv : 0 ≤ v)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (hE : ∀ A ∈ M, spectralNorm (E A) ≤ v)
    (z : List (Square d)) (hz : WordIn M z) :
    spectralNorm (matrixProduct (z.map (fun A => C A + E A))) ≤
      K * (u + K * v) ^ z.length := by
  let w := productEnvelope M C u
  have hK0 : 0 ≤ K := by linarith
  have hw := productEnvelope_isComplexNorm M C u K hu hC
  have hb := productEnvelope_bounds M C u K hu hC
  have hr : 0 ≤ u + K*v := by positivity
  have hD : ∀ A ∈ M, ∀ x, w (applyMatrix (C A + E A) x) ≤ (u+K*v) * w x := by
    intro A hA x
    rw [applyMatrix_add]
    calc
      w (applyMatrix (C A) x + applyMatrix (E A) x) ≤
          w (applyMatrix (C A) x) + w (applyMatrix (E A) x) := hw.2.2.1 _ _
      _ ≤ u * w x + K * ‖applyMatrix (E A) x‖ :=
        add_le_add (productEnvelope_generator M C u K hu hC A hA x) (hb _).2
      _ ≤ u * w x + K * (v * ‖x‖) := by
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left ((norm_applyMatrix_le (E A) x).trans
            (mul_le_mul_of_nonneg_right (hE A hA) (norm_nonneg x))) hK0)
      _ ≤ u * w x + K * (v * w x) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hb x).1 hv) hK0)
      _ = (u+K*v) * w x := by ring
  apply (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ) _).opNorm_le_bound (by positivity)
  intro x
  calc
    ‖applyMatrix (matrixProduct (z.map (fun A => C A + E A))) x‖ ≤
        w (applyMatrix (matrixProduct (z.map (fun A => C A + E A))) x) := (hb _).1
    _ ≤ (u+K*v) ^ z.length * w x :=
      norm_product_from_generator M _ w _ hr hD z hz x
    _ ≤ (u+K*v) ^ z.length * (K * ‖x‖) :=
      mul_le_mul_of_nonneg_left (hb x).2 (pow_nonneg hr _)
    _ = (K * (u+K*v) ^ z.length) * ‖x‖ := by ring

lemma interspersed_zero_rate {d : ℕ} (M : Set (Square d))
    (C E : Square d → Square d) (K v : ℝ) (hK : 1 ≤ K) (hv : 0 ≤ v)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * (0 : ℝ) ^ z.length)
    (hE : ∀ A ∈ M, spectralNorm (E A) ≤ v)
    (z : List (Square d)) (hz : WordIn M z) :
    spectralNorm (matrixProduct (z.map (fun A => C A + E A))) ≤
      K * (K*v) ^ z.length := by
  have hK0 : 0 ≤ K := by linarith
  have hCv : ∀ A ∈ M, C A = 0 := by
    intro A hA
    have h := hC [A] ((WordIn_cons_iff M A []).mpr ⟨hA, WordIn_nil M⟩)
    apply (spectralNorm_eq_zero_iff (C A)).mp
    exact le_antisymm (by simpa using h) (spectralNorm_nonneg _)
  induction z with
  | nil => simpa using hC [] (WordIn_nil M)
  | cons A z ih =>
      obtain ⟨hA, hz⟩ := (WordIn_cons_iff M A z).mp hz
      have hvK : v ≤ K*v := by nlinarith
      simp only [List.map_cons, matrixProduct_cons, List.length_cons, hCv A hA, zero_add]
      calc
        spectralNorm (matrixProduct (z.map (fun A => C A + E A)) * E A) ≤
            spectralNorm (matrixProduct (z.map (fun A => C A + E A))) * spectralNorm (E A) :=
          spectralNorm_mul_le _ _
        _ ≤ (K * (K*v)^z.length) * (K*v) :=
          mul_le_mul (ih hz) ((hE A hA).trans hvK) (spectralNorm_nonneg _)
            (mul_nonneg hK0 (pow_nonneg (mul_nonneg hK0 hv) _))
        _ = K * (K*v)^(z.length+1) := by rw [pow_succ]; ring

theorem interspersed_product_bound {d : ℕ} (M : Set (Square d))
    (C E : Square d → Square d) (K u v : ℝ) (hK : 1 ≤ K)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hC : ∀ z : List (Square d), WordIn M z →
      spectralNorm (matrixProduct (z.map C)) ≤ K * u ^ z.length)
    (hE : ∀ A ∈ M, spectralNorm (E A) ≤ v)
    (z : List (Square d)) (hz : WordIn M z) :
    spectralNorm (matrixProduct (z.map (fun A => C A + E A))) ≤
      K * (u + K * v) ^ z.length := by
  by_cases hu0 : u = 0
  · subst u
    simpa using interspersed_zero_rate M C E K v hK hv hC hE z hz
  · exact interspersed_positive_rate M C E K u v hK (lt_of_le_of_ne hu (Ne.symm hu0))
      hv hC hE z hz

#print axioms interspersed_product_bound
#assert_trust kernel interspersed_product_bound

end NLA.MF07
