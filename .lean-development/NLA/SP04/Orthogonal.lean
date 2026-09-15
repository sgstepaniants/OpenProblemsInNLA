/-
Mathematical counterexample: Matthew J. Colbrook, University of Cambridge DAMTP.
Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology. Apache 2.0; AI-assisted.
Exact orthogonal changes preserve the full stationary relation and Frobenius norm.
-/
import NLA.SP04.Frobenius

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option leancert.trust "kernel"
open scoped BigOperators
noncomputable section
namespace NLA.SP04

lemma orthogonal_transpose {n : ℕ} (P : Mat n) (hP : Orthogonal P) :
    Orthogonal P.transpose := by
  simpa only [Orthogonal, Matrix.transpose_transpose] using And.intro hP.2 hP.1

lemma orthogonal_mul {n : ℕ} (P Q : Mat n) (hP : Orthogonal P) (hQ : Orthogonal Q) :
    Orthogonal (P * Q) := by
  constructor
  · calc
      (P * Q).transpose * (P * Q) = Q.transpose * (P.transpose * P) * Q := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hP.1]; simpa only [Matrix.mul_one] using hQ.1
  · calc
      (P * Q) * (P * Q).transpose = P * (Q * Q.transpose) * P.transpose := by
        rw [Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQ.2]; simpa only [Matrix.mul_one] using hP.2

lemma orthogonal_abs_det {n : ℕ} (P : Mat n) (hP : Orthogonal P) : |P.det| = 1 := by
  have hdet : P.det * P.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one]
      using congrArg Matrix.det hP.1
  apply (sq_eq_sq₀ (abs_nonneg P.det) (by norm_num : (0 : ℝ) ≤ 1)).mp
  simpa only [sq_abs, pow_two, one_mul] using hdet

lemma unit_absolute_determinant_orthogonal {n : ℕ} (P Q X : Mat n)
    (hP : Orthogonal P) (hQ : Orthogonal Q) :
    UnitAbsoluteDeterminant (P * X * Q.transpose) ↔ UnitAbsoluteDeterminant X := by
  simp only [UnitAbsoluteDeterminant, Matrix.det_mul, Matrix.det_transpose, abs_mul,
    orthogonal_abs_det P hP, orthogonal_abs_det Q hQ, one_mul, mul_one]

lemma orthogonal_inverse_forward {n : ℕ} (P Q X : Mat n)
    (hP : Orthogonal P) (hQ : Orthogonal Q) :
    P.transpose * (P * X * Q.transpose) * Q = X := by
  calc
    P.transpose * (P * X * Q.transpose) * Q =
        (P.transpose * P) * X * (Q.transpose * Q) := by noncomm_ring
    _ = X := by rw [hP.1, hQ.1, Matrix.one_mul, Matrix.mul_one]

lemma orthogonal_forward_inverse {n : ℕ} (P Q X : Mat n)
    (hP : Orthogonal P) (hQ : Orthogonal Q) :
    P * (P.transpose * X * Q) * Q.transpose = X := by
  calc
    P * (P.transpose * X * Q) * Q.transpose =
        (P * P.transpose) * X * (Q * Q.transpose) := by noncomm_ring
    _ = X := by rw [hP.2, hQ.2, Matrix.one_mul, Matrix.mul_one]

lemma frobenius_orthogonal {n : ℕ} (P Q A : Mat n)
    (hP : Orthogonal P) (hQ : Orthogonal Q) :
    frobeniusNorm (P * A * Q.transpose) = frobeniusNorm A := by
  apply (sq_eq_sq₀ (frobenius_norm_squared _).1 (frobenius_norm_squared _).1).mp
  rw [frobenius_norm_sq_trace, frobenius_norm_sq_trace]
  have hgram : (P * A * Q.transpose).transpose * (P * A * Q.transpose) =
      Q * (A.transpose * A) * Q.transpose := by
    calc
      (P * A * Q.transpose).transpose * (P * A * Q.transpose) =
          Q * A.transpose * (P.transpose * P) * A * Q.transpose := by
            simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
            noncomm_ring
      _ = Q * (A.transpose * A) * Q.transpose := by
        rw [hP.1, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
  rw [hgram, Matrix.trace_mul_cycle, hQ.1, Matrix.one_mul]

lemma stationary_orthogonal_forward {n : ℕ} (P Q U X : Mat n) (c : ℝ)
    (hP : Orthogonal P) (hQ : Orthogonal Q) (hX : StationaryPair U X c) :
    StationaryPair (P * U * Q.transpose) (P * X * Q.transpose) c := by
  refine ⟨(unit_absolute_determinant_orthogonal P Q X hP hQ).mpr hX.1, ?_⟩
  calc
    (P * X * Q.transpose).transpose *
        (P * U * Q.transpose - P * X * Q.transpose) =
        Q * X.transpose * (P.transpose * P) * (U - X) * Q.transpose := by
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
      noncomm_ring
    _ = Q * (X.transpose * (U - X)) * Q.transpose := by
      rw [hP.1, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
    _ = Q * (c • (1 : Mat n)) * Q.transpose := by rw [hX.2]
    _ = c • (1 : Mat n) := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hQ.2]

lemma stationary_orthogonal_transport {n : ℕ} (P Q U X : Mat n) (c : ℝ)
    (hP : Orthogonal P) (hQ : Orthogonal Q) :
    StationaryPair (P * U * Q.transpose) X c ↔
      StationaryPair U (P.transpose * X * Q) c := by
  constructor
  · intro h
    have ht := stationary_orthogonal_forward P.transpose Q.transpose
      (P * U * Q.transpose) X c (orthogonal_transpose P hP) (orthogonal_transpose Q hQ) h
    simp only [Matrix.transpose_transpose] at ht
    rw [orthogonal_inverse_forward P Q U hP hQ] at ht
    exact ht
  · intro h
    have ht := stationary_orthogonal_forward P Q U (P.transpose * X * Q) c hP hQ h
    rw [orthogonal_forward_inverse P Q X hP hQ] at ht
    exact ht

lemma frobenius_distance_orthogonal_transport {n : ℕ} (P Q U X : Mat n)
    (hP : Orthogonal P) (hQ : Orthogonal Q) :
    frobeniusDistance (P * U * Q.transpose) X =
      frobeniusDistance U (P.transpose * X * Q) := by
  have hdiff : P * U * Q.transpose - X = P * (U - P.transpose * X * Q) * Q.transpose := by
    rw [Matrix.mul_sub, Matrix.sub_mul, orthogonal_forward_inverse P Q X hP hQ]
  unfold frobeniusDistance
  rw [hdiff, frobenius_orthogonal P Q _ hP hQ]

lemma unique_least_orthogonal_forward {n : ℕ} (P Q U X : Mat n) (c : ℝ)
    (hP : Orthogonal P) (hQ : Orthogonal Q) (h : UniqueLeastAbsoluteMultiplier U X c) :
    UniqueLeastAbsoluteMultiplier (P * U * Q.transpose) (P * X * Q.transpose) c := by
  refine ⟨⟨stationary_orthogonal_forward P Q U X c hP hQ h.1.1, ?_⟩, ?_⟩
  · intro Y d hY
    exact h.1.2 (P.transpose * Y * Q) d
      ((stationary_orthogonal_transport P Q U Y d hP hQ).mp hY)
  · intro Y d hY hd
    obtain ⟨hYX, hdc⟩ := h.2 (P.transpose * Y * Q) d
      ((stationary_orthogonal_transport P Q U Y d hP hQ).mp hY) hd
    refine ⟨?_, hdc⟩
    calc
      Y = P * (P.transpose * Y * Q) * Q.transpose :=
        (orthogonal_forward_inverse P Q Y hP hQ).symm
      _ = P * X * Q.transpose := by rw [hYX]

theorem orthogonal_covariance {n : ℕ} (P Q U X : Mat n) (c : ℝ)
    (hP : Orthogonal P) (hQ : Orthogonal Q) :
    (UnitAbsoluteDeterminant (P.transpose * X * Q) ↔ UnitAbsoluteDeterminant X) ∧
    (StationaryPair (P * U * Q.transpose) X c ↔
      StationaryPair U (P.transpose * X * Q) c) ∧
    frobeniusDistance (P * U * Q.transpose) X =
      frobeniusDistance U (P.transpose * X * Q) ∧
    (UniqueLeastAbsoluteMultiplier (P * U * Q.transpose) X c ↔
      UniqueLeastAbsoluteMultiplier U (P.transpose * X * Q) c) := by
  refine ⟨?_, stationary_orthogonal_transport P Q U X c hP hQ,
    frobenius_distance_orthogonal_transport P Q U X hP hQ, ?_⟩
  · simpa only [Matrix.transpose_transpose] using
      unit_absolute_determinant_orthogonal P.transpose Q.transpose X
        (orthogonal_transpose P hP) (orthogonal_transpose Q hQ)
  · constructor
    · intro h
      have ht := unique_least_orthogonal_forward P.transpose Q.transpose
        (P * U * Q.transpose) X c (orthogonal_transpose P hP) (orthogonal_transpose Q hQ) h
      simp only [Matrix.transpose_transpose] at ht
      rw [orthogonal_inverse_forward P Q U hP hQ] at ht
      exact ht
    · intro h
      have ht := unique_least_orthogonal_forward P Q U (P.transpose * X * Q) c hP hQ h
      rw [orthogonal_forward_inverse P Q X hP hQ] at ht
      exact ht

#assert_trust kernel orthogonal_covariance
#print axioms orthogonal_covariance
end NLA.SP04
