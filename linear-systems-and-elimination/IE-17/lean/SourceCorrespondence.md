# IE-17 statement and source correspondence

This document concerns the full frozen target, not just the finite numerical
certificates. The canonical problem and source manuscript were read at upstream
commit `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`:

* [IE-17 canonical statement](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/8f04b905eb2e0827b6b84f37d9d080ae1f05b202/linear-systems-and-elimination/IE-17/README.md).
* [Matthew J. Colbrook, An exact spectral backward-error counterexample for LSMR](https://github.com/ajt60gaibb/OpenProblemsInNLA/blob/8f04b905eb2e0827b6b84f37d9d080ae1f05b202/references/colbrook-recovered-2026-09-11/manuscripts/IE-17.tex).

Original mathematics: Matthew J. Colbrook, Department of Applied Mathematics and
Theoretical Physics, University of Cambridge. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA, with substantial AI assistance.

All names below are in namespace `NLA.IE17`. The independent Challenge contains
exactly seventeen targets; its deliberate placeholders are compiled separately
and are never imported by Solution.

| Export | Mathematical content and source relationship |
|---|---|
| `euclideanNorm_sq` | Identifies the actual `EuclideanSpace` norm squared with the finite sum of squares. Prevents using the default function-space supremum norm. |
| `backwardError_isLeast` | For arbitrary real dimensions/data, the actual matrix-only feasible norm set is nonempty and its real infimum is an attained minimum. This supplies a necessary existence bridge for the manuscript's minimum notation and later strict lower bound. |
| `backwardError_zero_at_solution` | The original exact-normal-solution convention follows from the zero feasible perturbation and nonnegativity. |
| `augmentedPseudoinverse_spec` | For nonzero iterate and residual, proves invertibility of the actual augmented Gram matrix and all four Moore–Penrose identities for its Gram-inverse formula. |
| `projectionError_sq_formula` | Derives the source §1 scalar inverse expression from the actual augmented orthogonal projection norm. The expression is not assumed as the definition of the error. |
| `witness_full_column_rank` | The source's actual 4-by-3 matrix has full column rank; its zero fourth row does not invalidate the least-squares instance. |
| `witness_iterates` | Certifies all three source §1 exact iterates by membership and universal minimum-normal-residual optimization over the entire Krylov space, including the minimum-length tie convention. |
| `witness_before_termination` | The first two iterates are nonzero and their normal residuals are nonzero; the third reaches the exact least-squares solution. |
| `upperPerturbation_certificate` | The source §4 fully rational matrix is genuinely feasible with b fixed and has squared induced Euclidean operator norm at most 1979/2000. Exact positive Gram factorization is connected to the operator norm. |
| `lowerCertificate_positive` | The source §3 convex matrix minus 99/100 times identity is exactly K/2407881992100, and the displayed integer K is positive definite. |
| `every_second_perturbation_large` | Every feasible real 4-by-3 perturbation at the second iterate has squared spectral norm strictly greater than 99/100, including perturbations of any rank and the zero-new-residual case. |
| `witness_backwardError_separation` | Attainment and the two certificates yield the source §3 strict separation of the actual two optimization-defined backward errors. |
| `witness_projectionError_exact` | Gives exactly both large rational projected-error squares in source §4, after the general pseudoinverse/projection bridge. |
| `witness_projectionError_separation` | Rational comparison proves the source §4 cutoffs 1.006 and 1.007, represented exactly as 503/500 and 1007/1000. |
| `counterexample` | Gives a genuine successive nonzero pair of exact LSMR iterates and strict increases of both original error quantities. |
| `not_spectralMonotonicity` | Negates the complete canonical spectral backward-error monotonicity proposition over arbitrary real data and allowed successive iterates. |
| `not_projectionMonotonicity` | Negates the complete canonical projected-error monotonicity proposition with the same iteration/stopping conventions. |

The definitions use undamped, zero-start LSMR. With `H=AᵀA` and `g=Aᵀb`, its
Krylov space is `span{Hʲg : 0≤j<k}`. An iterate minimizes `‖g−Hx‖₂` over every
real vector in that span and has minimum length among minimizers. The witness
proof establishes these universal clauses rather than substituting a computed
list of iterates, an unrelated objective, or a floating-point recurrence.

`FeasiblePerturbation A b x E` is exactly
`(A+E)ᵀ((A+E)x−b)=0`, over every real matrix E of the correct size; b is held
fixed. `spectralNorm` uses `Matrix.Norms.L2Operator`, the induced Euclidean norm.
The finite-dimensional compactness argument proves the minimum is attained
before a strict bound on every E is transferred to that minimum. It does not
infer strictness of an infimum merely from pointwise strict inequalities.

The augmented matrix is exactly `K=[A; (‖r‖₂/‖x‖₂)I]` with `r=b−Ax`, and the
error is the norm of `K K† [r;0]`, divided by `‖x‖₂`. Sum indexing represents
vertical stacking. The Gram-inverse candidate for K† is justified by all four
Penrose identities before use. The canonical exact-solution branch has error
zero. Comparisons concern nonzero iterates, so no totalized division at x=0 is
used to produce the counterexample.

The proof uses two equivalent computational improvements. First, rational LDL
factorizations replace expansion of leading determinants; Lean checks each
factorization, positivity and injectivity. The lower pivots are scaled for the
integer matrix K itself, and the separate rational scale is proved explicitly.
Second, the lower-bound proof uses the unnormalized new residual d. Its exact
orthogonality equations imply
`‖x‖₂² dᵀD d = ‖d‖₂² ‖r−d‖₂²`; operator bounds then control both quadratic
forms in the source's convex combination. This avoids normalization and all
interval computations while preserving the universal perturbation argument.
The d=0 branch is proved separately, using the actual witness residual bound.

The source's dense Hadamard-transformed variant is not required and is not
claimed. Nor are a Frobenius-norm formulation, perturbations to b, or stability of
floating-point LSMR claimed. The full-column-rank witness satisfies the original
target without any of those changes.

The complete source graph and all seventeen exported LeanCert assertions passed
development Linux run 35017536835 at
`8070ed199166429ffd5ea3091caa940de6af5568`, with only the standard three measured
axioms. This development execution did not run Comparator or export/default
kernel replay. Those canonical checks and the final two compiled-byte referee
addenda remain required before the package is counted as fully verified.
