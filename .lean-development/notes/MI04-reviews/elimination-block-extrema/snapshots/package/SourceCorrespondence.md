# MI-04 source correspondence and API plan

This is an unreviewed statement-only draft. All entries name obligations, not established results. Original proof: Matthew J. Colbrook, University of Cambridge DAMTP. Formalization: George Stepaniants, California Institute of Technology CMS.

| Challenge obligations | Original source and proposed exact role |
|---|---|
| topValue_maximum; positive_quadratic_iff; positive_norm_eq_top; shifted_topValue; scalar_order_iff_top; unitary_topValue | Basic actual finite-dimensional Rayleigh, PSD and Euclidean norm facts needed by source subsection1. They make the auxiliary supremum and positivity meanings explicit. |
| pencil_isHermitian; universal_to_extreme_symmetry | Source subsection1, (1) to (2) to (3). All actual PSD completions remain in the initial hypothesis; bI+K and the sign-flip unitary supply the inequalities. |
| extreme_symmetry_scaled_unitary | Source subsection2, positive scaling and arbitrary changes of orthonormal basis. |
| simple_peak_sandwich; simple_peak_second_order | Exact variational replacement for source equations (1.1)–(1.2). The same coefficient follows from one explicit test vector and a universal weighted-square upper bound. Repeated nonmaximal values are allowed. No analyticity result is assumed. |
| weighted_magnitude_identity; offDiagonal_magnitude_symmetry | Source weighted identity and its single-weight variation. Only the diagonal probes with other values 0 or one value 1/2 are needed. |
| orthonormal_pair_symmetry; pair_symmetry_normal | Source pair condition and normality argument over every completed orthonormal basis. |
| normal_unitary_diagonalization; pair_symmetry_unitary | Source normal spectral theorem and basis change. The normal diagonalization is an explicit full obligation, to be derived from the commuting Hermitian parts and pinned joint-eigenspace/subordinate-basis results. |
| diagonal_pair_collinearity; collinear_values_affine | Source triple collinearity and actual affine-line reconstruction, including all repeated values and dimensions1/2. Equivalent vectors (1,1,1) and (1,I,-1-I) eliminate cube-root-of-unity algebra. |
| pair_symmetry_essentially_hermitian | Conjugate the real affine coordinates back to an actual Hermitian K; scalar matrices included. |
| universal_positive_block_essentially_hermitian | Entire original canonical implication in every n>=1. The universal A/B premise and explicit alpha K+beta I conclusion are visible in the declaration. |

The original converse and four-way equivalence are outside the proposed claim. No prior normality theorem with nonsingularity or distinct singular values is used. No default matrix norm, restricted completion class or selected eigenpair replaces the full target.

## Pinned reusable foundations inspected

All Mathlib references use revision 0df444a360eaa60ab8c11dca51a86af692955474. API-PROVENANCE.json binds the complete files containing the inspected APIs.

- Analysis/CStarAlgebra/Matrix.lean: actual Matrix.toEuclideanCLM and induced Euclidean norm; existing MF-24 definitions supply the same explicit norm pattern.
- Analysis/InnerProductSpace/Rayleigh.lean: real quadratic form, norm comparison, finite-dimensional extrema/eigenvector relations. The proof route can use direct compactness plus these existing bounds.
- Analysis/Matrix/Order.lean and LinearAlgebra/Matrix/PosDef.lean: actual PSD order, quadratic-form characterization and congruences. SP-05's verified complex positivity work supplies a related API example; no SP-05 theorem is assumed here.
- Analysis/Matrix/Spectrum.lean: Hermitian orthonormal eigenbases and actual unitary diagonalization, with no distinct-value assumption.
- Analysis/InnerProductSpace/Adjoint.lean: isStarNormal_iff_norm_eq_adjoint.
- LinearAlgebra/Complex/Module.lean: commuting real/imaginary-part characterization of normality.
- Analysis/InnerProductSpace/JointEigenspace.lean: orthogonality and internal direct sum of simultaneous eigenspaces for commuting Hermitian operators.
- Analysis/InnerProductSpace/PiL2.lean: extension to orthonormal bases and DirectSum.IsInternal.subordinateOrthonormalBasis for the orthogonal simultaneous-eigenspace decomposition.

The simple-peak sandwich and the final normal-matrix diagonalization bridge are substantive new developments, not existing lemmas silently cited as proved. Two independent reviewers must approve the complete route and signatures before implementation.
