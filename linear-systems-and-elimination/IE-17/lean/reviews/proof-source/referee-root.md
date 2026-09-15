# IE-17 independent proof-source referee

Reviewer `/root`, AI agent, 2026-09-15. This is scoped Tau Ceti independent source
review, not human peer review or final mechanical verification. I did not author
the mathematics, definitions, Challenge or proof modules. I coordinated exact
source snapshots and compiler diagnostics. REVIEW.json binds the source snapshot
at development commit 236d828d0a951b75b07ee31813cdcf8567b25815.

**Source verdict: approve the intended mathematics and complete canonical scope;
final verification pending.** The previous Linux run accepted Geometry and
Attainment but rejected later proof modules. Those real errors are being repaired;
no source review or printed theorem statement is counted as kernel acceptance.
The separate final Comparator and rejection-control run has not occurred.

I read the full definitions, Geometry, Attainment, ExactData, Iterates,
ProjectionAlgebra, Projection, Quadratic, Certificates, LowerBound, Final and
Solution. I compared the complete route with the frozen 17 independent Challenge
exports, the prior source/statement review and the original canonical IE-17
problem. Compiler repairs reduce finite matrix entries, supply an existing
real-order instance and make elementary coordinate equalities explicit; they
do not replace any mathematical object or narrow a quantifier.

The vector norm is explicitly Euclidean via WithLp, and the matrix norm is the
induced Euclidean operator norm selected at definition time. Geometry supplies
the squared-coordinate and operator-norm bridges, including the transpose
identity. The perturbation feasible set permits every real E with b fixed and
uses the actual perturbed normal equations. Nonemptiness is proved using -A.
Attainment first restricts to the closed feasible subset inside the ball of
radius ||-A||, then proves its minimizer is minimal against every outside
perturbation as well. This justifies strictness for the actual infimum rather
than incorrectly taking a strict pointwise bound through an unattained infimum.

Iterates proves membership in the true Krylov spans using exact generator
representations, extends orthogonality to each whole span, and establishes the
Pythagorean identity and uniqueness of the normal-residual minimizer. The
minimum-length tie rule is consequently satisfied rather than omitted. Stages
0,1,2,3, nonzero compared iterates and exact termination are all explicit.
The witness has full column rank, but no full-rank restriction is inserted
into the original universal monotonicity conjectures.

The upper backward-error bound uses a specific genuine feasible rational E
and an exact Gram certificate for its true operator norm. The lower bound
covers every feasible E. It splits zero and nonzero new residuals, deriving
E*x=r-d and the perturbed orthogonality relation. Multiplying by the squared
length of d avoids a numerical square-root normalization. The two quadratic
bounds combine with weights 5/6 and 1/6 and the positive-definite gap certificate.
Attainment then yields the strict inequality at the true backward error.

The independent referee found an omitted factor 2407881992100 in the initial
LDL certificate. The repaired pivots are for the exact frozen integer matrix,
not its rescaled version. The source now uses the correct scale; the other
referee independently checked all 16 entries and positive pivots with exact
Fractions. The forthcoming Lean equality and positivity proofs remain mandatory.
Neither Python formatting nor a source review is assumed as a theorem.

The projection definition is the actual augmented Moore-Penrose projection.
ProjectionAlgebra proves positive definiteness of the augmented Gram matrix
under the original nonzero conditions, all four Penrose identities, and its
Euclidean projection-norm identity. Projection derives the scalar rational
formula only afterward; the convenient formula is not substituted into the
definition. Both witness fractions and separating cutoffs are exact rational
claims. The normal-residual-zero convention and positivity needed to pass from
squared comparisons to norm comparisons are explicitly handled.

Final supplies one pair of genuine successive iterates where both errors
strictly increase and refutes both complete universal claims. There is no
replacement by residual-norm monotonicity, a Frobenius norm, a restricted
perturbation class or an approximate LSMR recurrence. All 17 exported obligations
have implementation declarations and LeanCert kernel assertions; elaborated
type equality and transitive permitted axioms still require actual Comparator.

Proof modules separate general norm/compactness/projection algebra from the
small exact witness. This avoids interval subdivision and numerical inversion.
Mathlib supplies finite-dimensional compactness, operator norms, PSD and matrix
inverse APIs; no unsupported analytic lemma has been moved into a hypothesis.
The fixed rational LDL data can remain private proof helpers. Publication must
retain the source attribution, the resolved review finding and honest build
evidence, remove obsolete draft-status prose and select Solution for the usual
standalone build.

Colbrook retains mathematical credit and Cambridge DAMTP affiliation. George
Stepaniants has formalization credit and Caltech Computing and Mathematical
Sciences affiliation, without email. Two AI-agent reviews are not human peer
review. A final addendum must bind the actual accepted source bytes and identify
the real Linux/kernel/Comparator logs inspected before any verified status.
