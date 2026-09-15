/-
Copyright (c) 2026 George Stepaniants. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Stepaniants

Rational witness certificate data transcribed from independently checked
source arithmetic. Python only formats constants; Lean proves every identity,
positive pivot, injectivity statement, feasibility and spectral-norm bridge.
No finite numerical checker is assumed as a theorem.
Supplementary source SHA256: 278cc6756f2499e84af5dc47b916cfb6a1320184ebc675fb8bbf30a6e80ec0c6
-/
import NLA.IE17.Quadratic
import NLA.IE17.ExactData

set_option autoImplicit false
set_option leancert.trust "kernel"
open scoped BigOperators Classical Matrix.Norms.L2Operator
noncomputable section
namespace NLA.IE17

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

def upperExact : Mat 4 3 :=
  !![(-82605007467565780 / 83605574761527903), (1935141443699540 / 27868524920509301), (421707455855450 / 27868524920509301);
    (39351326577989 / 167211149523055806), (-11644520940683327 / 27868524920509301), (-17771148162006125 / 55737049841018602);
    (-10780617925213 / 83605574761527903), (11977623324684560 / 27868524920509301), (9139875006794090 / 27868524920509301);
    (-6175589313810285 / 55737049841018602), (-12599865024711003 / 27868524920509301), (-19466291678089345 / 55737049841018602)]

theorem upperPerturbation_explicit : upperPerturbation = upperExact := by
  unfold upperPerturbation upperC0 upperA0 upperH
  simp only [witness_residual_one, witnessA_mulVec, witnessAt_mulVec]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperExact, upperCutoff, witnessW, witnessA, witnessB, witnessX1, outer,
      normSq, realDot, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

def upperFactor : Mat 3 3 :=
  !![1, (589582761960115650204097482000 / 32082903136661873741517122683), (-106612695230984315281013395000 / 4583271876665981963073874669);
    0, 1, (35116855505169327891330000 / 2526440607887109017861870683);
    0, 0, 1]

def upperPivots : Vec 3 :=
  ![(32082903136661873741517122683 / 31584381671763314443807585554000),
    (4999825963008588746348642081657 / 64165806273323747483034245366000),
    (1643701075719490133637293519971 / 15158643647322654107171224098000)]

theorem upperFactor_injective : Function.Injective upperFactor.mulVec := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  norm_num [upperFactor, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2
  ext i
  fin_cases i
  · change x 0 = y 0
    linarith
  · change x 1 = y 1
    linarith
  · change x 2 = y 2
    exact h2


theorem upperPivots_positive : (Matrix.diagonal upperPivots).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [upperPivots]

theorem upper_gram_factorization :
    upperCutoff • (1 : Mat 3 3) - upperPerturbation.transpose * upperPerturbation =
      upperFactor.transpose * Matrix.diagonal upperPivots * upperFactor := by
  rw [upperPerturbation_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [upperExact, upperCutoff, upperFactor, upperPivots,
      Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply, Fin.sum_univ_succ]

theorem upper_gram_positive :
    (upperCutoff • (1 : Mat 3 3) - upperPerturbation.transpose * upperPerturbation).PosDef := by
  rw [upper_gram_factorization]
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    upperPivots_positive.conjTranspose_mul_mul_same upperFactor_injective

theorem upper_feasible :
    FeasiblePerturbation witnessA witnessB witnessX1 upperPerturbation := by
  unfold FeasiblePerturbation
  rw [upperPerturbation_explicit]
  ext i
  fin_cases i <;> norm_num [upperExact, witnessA, witnessB, witnessX1,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem upperPerturbation_certificate :
    FeasiblePerturbation witnessA witnessB witnessX1 upperPerturbation ∧
    (upperCutoff • (1 : Mat 3 3) - upperPerturbation.transpose * upperPerturbation).PosDef ∧
    spectralNorm upperPerturbation ^ 2 ≤ 1979 / 2000 := by
  refine ⟨upper_feasible, upper_gram_positive, ?_⟩
  exact spectralNorm_sq_le_of_gram_posSemidef upperPerturbation upperCutoff
    (by norm_num [upperCutoff]) upper_gram_positive.posSemidef

def lowerFactor : Mat 4 4 :=
  !![1, (-50293465200 / 206417059721), (1125984433750 / 206417059721), (-1435003762500 / 206417059721);
    0, 1, (99201725357988443265000 / 17265994657467102998545591), (-11093809772663000556250 / 2466570665352443285506513);
    0, 0, 1, (459864005326774119875642590032577100 / 3235492675893873171022706549421165963);
    0, 0, 0, 1]

def lowerPivots : Vec 4 :=
  ![206417059721,
    (17265994657467102998545591 / 206417059721),
    (960941324740480331793743845178086291011 / 17265994657467102998545591),
    (73447928333509818766233488267779425124360352091 / 1078497558631291057007568849807055321)]

theorem lowerFactor_injective : Function.Injective lowerFactor.mulVec := by
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  norm_num [lowerFactor, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h3
  ext i
  fin_cases i
  · change x 0 = y 0
    linarith
  · change x 1 = y 1
    linarith
  · change x 2 = y 2
    linarith
  · change x 3 = y 3
    exact h3


theorem lowerPivots_positive : (Matrix.diagonal lowerPivots).PosDef := by
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i <;> norm_num [lowerPivots]

theorem lower_integer_factorization :
    lowerIntegerMatrix = lowerFactor.transpose * Matrix.diagonal lowerPivots * lowerFactor := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [lowerIntegerMatrix, lowerFactor, lowerPivots,
      Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_succ]

theorem lowerCertificate_positive :
    lowerConvexMatrix - (99 / 100 : ℝ) • (1 : Mat 4 4) =
      (1 / 2407881992100 : ℝ) • lowerIntegerMatrix ∧
    lowerIntegerMatrix.PosDef := by
  constructor
  · have hcogram : witnessA * witnessA.transpose =
        ( !![1,0,0,0; 0,36,0,0; 0,0,25,0; 0,0,0,0] : Mat 4 4) := by
      ext i j
      rw [Matrix.mul_apply]
      fin_cases i <;> fin_cases j <;>
        norm_num [witnessA, Matrix.transpose_apply, Fin.sum_univ_succ]
    unfold lowerConvexMatrix lowerD
    simp only [hcogram, witness_residual_two, witnessA_mulVec]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [lowerIntegerMatrix, witnessB,
        witnessX2, normSq, outer, Matrix.mul_apply, Matrix.mulVec,
        dotProduct, Matrix.one_apply, Fin.sum_univ_succ]
  · rw [lower_integer_factorization]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      lowerPivots_positive.conjTranspose_mul_mul_same lowerFactor_injective

theorem lower_convex_gap_positive :
    (lowerConvexMatrix - (99 / 100 : ℝ) • (1 : Mat 4 4)).PosDef := by
  rw [lowerCertificate_positive.1]
  exact lowerCertificate_positive.2.smul (by norm_num)

#assert_trust kernel upperPerturbation_explicit
#assert_trust kernel upperPerturbation_certificate
#assert_trust kernel lowerCertificate_positive
#print axioms upperPerturbation_certificate
#print axioms lowerCertificate_positive

end NLA.IE17
