# MI-04 independent statement review

**Verdict: APPROVE the complete proposed mathematical boundary.** Actual Linux elaboration must still pass before the immutable freeze and proof implementation. This is not proof verification.

Reviewer: `/root`, independent non-implementing OpenAI Codex AI agent. I have written no MI-04 definition, specification or implementation. This review applies the repository's scoped Tau Ceti protocol, not an official service or external human peer review. I ran no local Lean, Lake, cache or compiled proof process.

## Reviewed boundary

I read the complete canonical question and Colbrook solution at upstream `ce47b5630bf3680d9211131c3a43825b022c139a`, all Definitions, all 21 Challenge declarations, numerical obligations, source correspondence, comparator configuration, dependency/project configuration and current metadata. The source/checksum reconciliation is retained in CHECKS.json.

- Definitions: `cfd0c1e0174699e8e9127a6fb8b7ce9de3f4c7d9770292746d15c0a5bc047748`.
- Challenge: `ca80d090bfe9f3013d08aa86297761e1e524810881bce92776896545d6eeabf9`.
- Numerical obligations: `5cb5e20ffcf035b2ea303cf9edae2e85619b0f562bf302cf6df0c7a46079d1d7`.

The final declaration explicitly quantifies every positive finite dimension and arbitrary complex X. Its premise ranges over every Hermitian A and B whose literal block matrix [A X; X* B] is positive semidefinite, and its conclusion produces an actual Hermitian K and complex alpha, beta with X=alpha K+beta I. It adds no nonsingularity, distinctness, positive-definiteness, genericity or bounded-data assumption. Scalar matrices and alpha=0 remain included. Formalizing the necessity implication completely answers the canonical question; the manuscript's additional converse and four-way equivalence are correctly outside the proposed claim.

## Definitions and all obligations

The norm is explicitly the norm of Matrix.toEuclideanCLM on complex EuclideanSpace. The full disjoint-sum block index retains both n-dimensional spaces. Positivity and Hermitian symmetry use the actual Mathlib predicates. `topValue` is the real supremum of all unit-vector quadratic forms. Its finite-dimensional attainment, scalar-shift, unitary-invariance, positivity and norm identifications are obligations, rather than assumptions embedded in a custom definition. The positive-dimensional hypotheses prevent an empty unit sphere in these claims.

The first six variational declarations establish these meanings. `pencil_isHermitian`, `universal_to_extreme_symmetry` and `extreme_symmetry_scaled_unitary` provide the source's completion and symmetry reduction. In particular, opposite diagonal blocks give nonnegative top extrema in positive dimension; the positive completion bI+K and the sign-flip unitary then compare both extremes. Scaling is restricted to positive real scalars only in an auxiliary theorem, without restricting the final input X.

I checked the two simple-peak claims algebraically. For the correction vector w, put S=||w||^2 and L=sum |V_ja|^2/(1-d_j). Since w_a=0 and V_aa=0, the exact quadratic form at e_a+epsilon w is 1+epsilon^2(S+L)+epsilon^3 Re(w*Vw), and its squared norm is 1+epsilon^2 S. Subtracting one from the quotient gives precisely the claimed lower expression. For an arbitrary unit vector c e_a+z, the upper estimate bounds the remainder perturbation by epsilon M||z||^2 and completes each square with weight 1-d_j-epsilon M. The smallness condition makes these weights greater than 1/4; dropping |c|^2<=1 gives the stated upper coefficient. This works even if nonmaximal diagonal values repeat or are very negative. Both coefficients converge to L, giving the one-sided squeeze. No eigenvalue analyticity, numerical spectral computation, unproved O-term or uniform neighborhood in V is assumed.

The weighted-identity and off-diagonal claims apply that result to both signs of the block pencil. The distinguished value 1 and remaining values in [-1/2,1/2] ensure the required simple peak in either sign. Choosing other diagonal entries first zero and then one selected entry 1/2 changes exactly one weight from 1 to 2/3, so equality forces the corresponding squared moduli to agree. The diagonal terms cancel. Arbitrary unitary invariance and orthonormal completion then give the pair condition; dimension one makes this intermediate pair condition vacuous but does not remove that dimension from the final result.

The remaining declarations explicitly require normality, full unitary diagonalization, invariance of the pair condition, collinearity of every triple, affine reconstruction and the actual Hermitian representation. No substantive normal spectral theorem is assumed as an extra hypothesis. The real/imaginary Hermitian parts and the pinned orthogonal joint-eigenspace APIs provide a plausible complete route without distinct eigenvalues. The triple vectors (1,1,1)/sqrt(3) and (1,I,-1-I)/2 have norm one and inner product zero. With a=z_i-z_k and b=z_j-z_k, the difference |a+Ib|^2-|a-Ib|^2 is 4 Im(a conjugate(b)), exactly the required orientation. Repeated indices or values give zero directly. The affine reconstruction handles either all equal values or a line through two distinct values, covering n=1, n=2 and zero eigenvalues.

## Reuse, computation and mechanical boundary

I inspected the pinned primary definitions of the Euclidean matrix operator and matrix positivity, and the joint-eigenspace decomposition API. The nine API-source hashes and all ten dependency revisions are reconciled in CHECKS.json. The direct normal-diagonalization bridge remains a substantive proof obligation. Neither source text nor a prospective library route establishes it yet.

Exact Rayleigh inequalities and rational probes replace analytic branches and interval subdivision. The alternative triple vectors avoid transcendental roots of unity. These are efficient changes of proof method with the same original conclusion. LeanCert kernel-trust assertions are required for all eventual exports; an artificial interval computation is unnecessary for an algebraic proof.

Comparator lists exactly the 21 independent Challenge declarations and no replaceable definitions. Its only permitted axioms are propext, Classical.choice and Quot.sound. The 21 intentional Challenge placeholders are specifications; no Solution exists and no proof may import them. Schema validity alone is not completed-project verification. Actual elaboration, immutable pre-proof recording, complete implementations, actual Linux Comparator/default-kernel/control results and two independent final referees remain necessary.

Original mathematical credit remains Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization credit is George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. AI assistance and the Forsythe/Schiffer structure references are disclosed; no George email or source-author endorsement is added. No canonical status, permanent ID or verified count is changed by this approval.
