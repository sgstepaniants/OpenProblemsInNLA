/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
AI-assisted formalization of Matthew J. Colbrook's SF-01 result, Cambridge DAMTP.

Typed real-to-complex matrix transport. Unit reflection follows from the
actual determinant, without a spectral or positive-weight premise.
-/
import NLA.SF01.Definitions

set_option autoImplicit false

namespace NLA.SF01
noncomputable section

lemma complexify_injective {n : ℕ} :
    Function.Injective (complexify : Square n → Matrix (Fin n) (Fin n) ℂ) := by
  intro A B h
  ext i j
  apply Complex.ofReal_injective
  exact congrFun (congrFun h i) j

lemma complexify_one (n : ℕ) :
    complexify (1 : Square n) = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  exact (Complex.ofRealHom.mapMatrix : Square n →+* Matrix (Fin n) (Fin n) ℂ).map_one

lemma complexify_sub {n : ℕ} (A B : Square n) :
    complexify (A - B) = complexify A - complexify B := by
  exact map_sub (Complex.ofRealHom.mapMatrix : Square n →+* Matrix (Fin n) (Fin n) ℂ) A B

lemma complexify_mul {n : ℕ} (A B : Square n) :
    complexify (A * B) = complexify A * complexify B := by
  exact (Complex.ofRealHom.mapMatrix : Square n →+* Matrix (Fin n) (Fin n) ℂ).map_mul A B

lemma complexify_smul {n : ℕ} (a : ℝ) (A : Square n) :
    complexify (a • A) = (a : ℂ) • complexify A := by
  ext i j
  change ((a * A i j : ℝ) : ℂ) = (a : ℂ) * (A i j : ℂ)
  exact Complex.ofReal_mul a (A i j)

lemma complexify_det {n : ℕ} (A : Square n) :
    (complexify A).det = (A.det : ℂ) := by
  exact (Complex.ofRealHom.map_det A).symm

lemma complexify_isUnit_iff {n : ℕ} (A : Square n) :
    IsUnit (complexify A) ↔ IsUnit A := by
  simp only [Matrix.isUnit_iff_isUnit_det, complexify_det,
    isUnit_iff_ne_zero, Complex.ofReal_eq_zero]

lemma complexify_spectralHomotopy {n : ℕ} (s : ℝ) (B : Square n) (t : ℝ) :
    complexify (spectralHomotopy s B t) =
      (s : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - (t : ℂ) • complexify B := by
  rw [spectralHomotopy, complexify_sub, complexify_smul, complexify_smul, complexify_one]

end
end NLA.SF01
