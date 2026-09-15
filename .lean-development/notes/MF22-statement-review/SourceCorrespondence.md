# MF-22 source correspondence

Source: the complete retained `matrix-functions-and-stability/MF-22/solution.md`
and original canonical README at upstream commit
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`. Exact copies and hashes are in
`source/` and `SOURCE-PROVENANCE.json`. The original mathematical proof and
this statement draft are attributed to George Stepaniants, Department of
Computing and Mathematical Sciences, California Institute of Technology.

This is a proof-free statement package. The Challenge placeholders establish
no mathematics. There are no source lemmas assumed as axioms, no accepted
Lean proof, no Comparator result and no change to the problem's status.

| Proposed declaration | Source and exact scope |
| --- | --- |
| `complex_entry_norm_bound` | Elementary finite-dimensional L2 norm bridge; applies to arbitrary finite complex matrix indices, including `Fin n × Fin 2`. |
| `source_entry_bound` | Original eight B/C blocks in the canonical README; loose bound `2+rho` for every dimension and every entry. |
| `leading_block_invertible` | Manuscript Section 1, `det L=24a`, nonzero for every real rho>0; actual inverse used in T and G. |
| `source_boundaries` | Section 1, equation (2), including exactly the three left zeros and `u_n=0`, without a condition on `v_n`. |
| `source_recurrence` | Section 1, equations (1)–(4), equivalent to the actual full Toeplitz system for every x and f. |
| `transfer_polynomial_certificates` | Section 2, equations (6)–(7), and Section 3, equation (15). Direct fixed-size determinant/cofactor identities replace the generating-function denominator inference. |
| `numerator_denominator_coprime` | Section 2, Lemma 1, every complex z and positive real parameter; all source exclusion branches retained. |
| `quartic_factorization` | Section 3, equation (12) and displayed q, q(1), q(-1). |
| `cayley_identity` | Section 3, equation (13), for complex x with the actual denominator nonzero. |
| `positive_discriminant_factor` | Exact real quadratic positivity used in equation (14); no interval or parameter restriction. |
| `real_cubic_discriminant` | Section 3, equation (14), and the nonzero inverse Cayley pole. |
| `exceptional_parameter` | Section 3's full rho²=10 case; the real quadratic and simple root -1 both retained. |
| `four_roots` | Section 3's full four distinct nonzero roots classification. The RootData existence is a theorem to prove, not a final assumed hypothesis. |
| `spectral_projector_algebra` | Section 3's diagonalizable transfer argument, represented by Lagrange polynomials evaluated at T; all four projectors and all powers including zero. |
| `dominant_projector` | Equation (16), absence of scalar pole cancellation, and Section 4's full rank-one projector identity. |
| `spectral_tail_bounds` | Equations (17)–(18), genuine spectral norm remainder and eventual denominator estimates. |
| `green_source_state` | Section 4, equation (19), all right-hand sides and all states through j=n, including recovery of every final v-coordinate. |
| `green_inverse` | Section 4's actual unique finite boundary solution; two-sided inverse, determinant nonzero and exact factor 80 in H inverse. |
| `uniform_green_entries` | Equations (19)–(21), all sizes past n0 and all indices j<=n, ell<n; cancellation of the growing terms required. |
| `eventual_inverse_entries` | Recovering u_j and v_j from the corresponding states, uniformly in every actual inverse entry. |
| `eventual_quadratic_conditioning` | Complete original polynomial-conditioning target, using exponent 2 instead of the source's stronger exponent 1. |
| `polynomial_conditioning` | The full original permanent MF-22 question, with every positive parameter, actual singular convention, eventual invertibility and real existential exponent. |

The simplification is limited to the last norm estimate. The original question
allows any nonnegative exponent. Bounding both norms by dimension times the
entry bound gives exponent 2, and avoids the bandwidth-uniform estimate for
the matrix itself. Every parameter, complex field, coefficient, boundary and
growing size remains unchanged. The package must not claim the source's
stronger linear estimate.

`checks/exact_source_algebra.py` performs exact Gaussian-integer polynomial
arithmetic with no dependencies. Its 14 diagnostics check proposed finite data,
including denominator-cleared 4×4 determinant and 3×3 cofactor formulas.
It is supplementary source checking, not a proof of the root classification,
uniform estimates, full target, or kernel acceptance. Its output cannot replace
any advertised Lean declaration.

The pinned Schiffer and Forsythe examples informed the independent Challenge,
statement-first workflow, numerical boundary and kernel-only LeanCert gates.
Mathlib's Lagrange, cubic discriminant, matrix characteristic polynomial,
actual inverse and genuine Euclidean matrix operator APIs are the intended
foundations. No theorem from another problem package is imported by this
statement draft. Reused implementation later must retain its attribution.

Before proof bodies: two independent statement reviews and actual Linux
elaboration, followed by an immutable hash freeze. Final acceptance requires
two independent referees on the complete implementation, all22 kernel trust
assertions, permitted-axiom audit, actual sandboxed Comparator, default-kernel
replay and rejection controls. These gates remain pending.
