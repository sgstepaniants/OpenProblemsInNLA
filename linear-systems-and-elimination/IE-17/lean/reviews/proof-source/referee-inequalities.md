# IE-17 independent proof-source review

Reviewer: Codex agent `/root/next_inequalities`, separate from the IE-17
implementation agent. Date: 15 September 2026. Scoped Tau Ceti checks were
applied to source correspondence, semantics, correctness, computation reduction,
trust separation and completeness. This is an AI-agent review, not human peer
review or a proof-assistant execution receipt.

**Disposition: one concrete numerical certificate defect was found and corrected;
no remaining substantive mathematical or scope objection in the inspected source.
Final verified acceptance remains withheld pending the actual Linux proof build,
LeanCert checks, Comparator, default-kernel replay and negative controls.**

All files in STATEMENT-FREEZE.json matched their frozen SHA-256 values at the
reviewed snapshot. The exact proof sources reviewed are bound by
REVIEWED-SOURCE-HASHES.json. No IE-17 source was edited by this reviewer, and no
local Lean or Lake command was run.

## Finding and correction

The original Certificates.lean used LDL pivots for K/2407881992100 while asserting
an unscaled factorization of K. Entry (0,0) already made the asserted identity
false: 206417059721 versus 206417059721/2407881992100. I reported the issue
immediately to the author and root. The author multiplied all four pivots by the
missing scale, retaining the original integer K and theorem target.

At corrected Certificates.lean SHA-256
7ed33746afbd198cab47b67026e6b4b911c39a5bb4c0250ba11cc5d2ea583d1d,
I separately parsed the ACTUAL Lean matrix and pivot literals using exact Python
fractions and verified all sixteen entries of K=L^T diag(pivots)L and all four
positive pivots. This supplementary diagnostic confirms the reported scaling
repair; it does not substitute for the Lean identity and positivity proofs.

## Original target and definitions

I read the canonical IE-17 README and complete Colbrook manuscript at upstream
8f04b905eb2e0827b6b84f37d9d080ae1f05b202, the frozen Definitions/Challenge/numerical
boundary, and every implementation module including the new Quadratic,
Certificates, LowerBound, Final and Solution files.

The two independent original monotonicity claims are both refuted on the same
successive first/second iterate pair. Matrix.Norms.L2Operator supplies the genuine
induced Euclidean operator norm. Vectors are explicitly sent through WithLp 2,
with a proved norm-squared coordinate bridge; no Pi supremum norm or Frobenius
matrix norm replaces the canonical norms. The right-hand side stays fixed.

IsLSMRIterate uses the canonical mathematical Krylov minimization specification,
including every real vector in the true span and the minimum-length tie rule.
The source explicitly presents this specification as equivalent to exact LSMR;
no different iterative method or floating-point recurrence is claimed.
SuccessiveNonzeroIterates requires nonzero compared iterates and a nonzero first
normal residual, while permitting termination at the second. The exhibited
pair additionally has both normal residuals nonzero, with exact termination at
the third iterate. Full column rank is proved for the witness and is not imposed
on either original universal conjecture.

FeasiblePerturbation retains the actual perturbed normal equations for every
real E, including rank-changing perturbations and zero new residual. backwardError
is the infimum over that full set, and its least-element theorem proves actual
attainment. There is no replacement by a computed finite witness set.

projectionError retains the augmented K, the projected augmented residual, and
division by the true Euclidean length of x. The chosen Gram inverse is justified
by invertibility and ALL FOUR Penrose equations on the relevant domain. The
projection-to-Gram scalar identity is a theorem, not a redefinition of the
approximation. Exact-solution conventions are preserved.

## Global optimization and strictness

Attainment.lean proves the feasible set closed from continuity of the actual
normal-equation map. It truncates only at the norm of the always-feasible -A,
obtains a compact nonempty subset, minimizes the continuous norm there, and
proves the minimizer also beats every feasible point outside the truncation.
The resulting IsLeast contract validates strict lower bounds on backwardError;
no unjustified strict-infimum argument remains.

Iterates.lean establishes exact membership at k=0,1,2,3. Orthogonality is extended
from each generating vector to the entire Krylov subspace using span induction.
The Pythagorean objective identity and injectivity of the diagonal Gram matrix
then prove global unique minimization, including all tie cases. Merely checking
candidate vectors is not used as a proxy for optimization.

Quadratic.lean derives the operator-norm bound from a semidefinite Gram
certificate using an actual continuous linear map between Euclidean spaces.
The first perturbation is checked against its actual rational completion,
feasibility, and a positive-definite Gram complement. No spectral-completion
lemma is imported as an assumption.

LowerBound.lean quantifies over every feasible E. If the new residual d is zero,
E*x=r and the induced operator-norm inequality gives the strict numerical lower
bound. If d is nonzero, perturbed normal equations give (A+E)^T*d=0 and
<d,b>=||d||^2. The exact D quadratic identity yields
s*<d,D*d>=||d||^2*||r-d||^2. Together with both true operator-norm inequalities,
the positive convex certificate gives the strict cutoff after canceling the
positive ||d||^2. Thus no residual direction, perturbation rank, or finite
selection is silently excluded. Actual attainment supplies a feasible minimizer
to which that strict universal bound applies.

The Penrose/Gram proof and positive diagonal inverse reduce the two projection
values to the stated exact rational numbers. Nonnegativity of both true errors
converts their squared strict separations to strict increases of the unsquared
quantities. Final.lean packages the same successive pair and explicitly derives
both universal-conjecture negations.

## Computation and trust

The reduction is appropriately aggressive: fixed rational LDL identities and
positive pivots replace eigenvalue estimation, exact quadratic identities avoid
unit-vector normalization, and the projection Gram formula removes square-root
interval arithmetic. There is no grid or interval subdivision. The substantial
finite arithmetic is supplementary certificate transcription; Lean is required
to prove the actual identities and positivity claims.

No implementation file imports Challenge. The final entry point asserts kernel
trust and prints axioms for all seventeen frozen exports. The Comparator config
lists those seventeen, no replaceable definitions, and only
propext/Classical.choice/Quot.sound. Source inspection found no custom axiom,
unsafe declaration, native_decide, admitted theorem or sorry in the implementation
closure. Definitions' prose mentioning an axiom is not an axiom declaration.
No proof-dependent definition weakens the frozen objects.

Original mathematics is credited to Matthew J. Colbrook, University of Cambridge
DAMTP. George Stepaniants receives the authorized Caltech Department of Computing
and Mathematical Sciences formalization credit, without his email. Historical
source authorship is retained.

The corrected source is suitable for continued mechanical checking. This report
cannot establish elaboration success or kernel acceptance. Actual logs, immutable
source receipts, final metadata/schema checks, negative controls and independent
final referee acceptance must precede counting or publication as Lean verified.
