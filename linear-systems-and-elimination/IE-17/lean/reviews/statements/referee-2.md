# IE-17 independent statement review

**Reviewer:** `/root/next_matrix_functions`, an independent Codex AI agent.
**Phase:** mathematical statement, definition, scope and exact-data review before
proof implementation. **Date:** 15 September 2026.

**Verdict: APPROVE the mathematical statement boundary at the hashes below.**
There is no outstanding mathematical scope or data finding. This is one
independent statement approval, not a claim of Lean type checking or proof
verification. A second independent approval and successful non-root Linux
type check are still required before the boundary is frozen and proof bodies
are implemented. AI-agent review is not human peer review or Tau Ceti endorsement.

I did not author or edit the IE-17 draft and did not use its author's numeric
checker or claimed PASS. I independently read the canonical page and complete
retained manuscript from immutable Git, read the actual draft definitions and all
17 Challenge statements, inspected the relevant pinned Mathlib norm definition,
and wrote and executed a separate exact rational checker. No local Lean/Lake
process, cache download, repository mutation or workflow operation was performed.

## Bound inputs

Upstream source is `ajt60gaibb/OpenProblemsInNLA` at commit
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`.

- `linear-systems-and-elimination/IE-17/README.md`.
- `references/colbrook-recovered-2026-09-11/manuscripts/IE-17.tex` (complete body).
- `references/colbrook-recovered-2026-09-11/submitted/proofs/IE-17.md` (complete
  mathematical text, as a second source rendering).

The reviewer recomputed the source hashes directly from Git; exact hashes are in
`CHECKS.json`. Historical reconstruction cautions in the retained manuscript were
treated as source history, not current instructions or evidence of formal status.

Reviewed draft directory:
`/tmp/nla-lean-next-20260915/elimination/IE-17`.

| File | SHA-256 |
|---|---|
| `NLA/IE17/Definitions.lean` | `97651aa5564143486e883b78b11425304580173ff4c76b35559351ebd438519c` |
| `Challenge.lean` | `6acb90f062712e404a9ec3bb899321c83840d813cf1ed46b2b997a9444cc4791` |
| `NUMERICAL_TARGETS.md` | `baef2552b8c076ec45223906c3a73c9e7724dc78b8b33e5dcf8aa8658556c074` |
| `comparator.json` | `fcd2ec8b560c611c4252413194da9702281f2a459943dec22a1386e0e46645d3` |

Dependency/configuration input hashes are also retained in `CHECKS.json`. Future
mathematical edits to these boundary definitions or signatures reopen this review.

## 1. Canonical norm and optimization semantics

The canonical question uses the **matrix-only spectral norm**, with b fixed.
`FeasiblePerturbation` is precisely the perturbed normal equation for every real
m-by-n E, without a rank restriction. The change in sign between a residual
b−(A+E)x and the normal equation written with (A+E)x−b has no effect on equality
to zero. No perturbation of b is introduced.

`spectralNorm` is elaborated in the explicitly opened
`Matrix.Norms.L2Operator` scope. I inspected pinned
`Mathlib/Analysis/CStarAlgebra/Matrix.lean`: `Matrix.l2_opNorm_def` identifies this
norm with the continuous-linear-map operator norm of `toEuclideanLin`; it is
not the Frobenius norm or an entrywise norm. The vector norm explicitly passes
through `WithLp.toLp 2` into EuclideanSpace, rather than using the default
function-space supremum norm. The squared-coordinate bridge is an exported
obligation, not assumed inside the numerical data.

`backwardError` is an actual real infimum of all feasible spectral norms.
The generic `backwardError_isLeast` statement requires **attainment**, which is
mathematically valid: E=−A is feasible, the polynomial normal-equation preimage
of zero is closed, the norm is continuous, and in finite dimensions a closed
feasible sublevel set with level ‖A‖ is nonempty and compact. Its minimum is the
minimum over the full feasible set. This closes the otherwise serious gap between
strict lower bounds for each feasible E and a strict lower bound for an infimum.
The generic statement also covers zero-dimensional vector spaces harmlessly;
the actual counterexample has the positive dimensions 4 and 3.

The canonical zero convention at a least-squares solution is properly represented:
`backwardError_zero_at_solution` is a proof obligation and `projectionError`
explicitly returns zero when the normal residual vanishes.

## 2. Exact LSMR and stopping

The Krylov generating family is exactly H^j g for j=0,...,k−1 with H=AᵀA and
g=Aᵀb. At k=0 its range is empty and its real span is {0}.
`IsLSMRIterate` requires membership, minimization of the actual Euclidean normal
residual over **all real vectors in that span**, and minimum Euclidean length
among all objective ties. It is not restricted to a finite candidate list and
does not substitute minimization of the residual b−Ax.

`SuccessiveNonzeroIterates` checks consecutive indices k,k+1, k≥1, both nonzero
iterates, and nontermination at the first. If exact termination had occurred at
an earlier index, nested Krylov spaces and the minimum-residual clause would
force that first normal residual to be zero, contradicting this condition.
The second iterate is allowed to terminate, as in the original question.
For the witness the stronger Challenge statement independently requires unique
minimizers at all four indices 0,1,2,3, and explicit termination at index 3.

I independently checked x1=(1021/31201)g and
x2=(16321g−383Hg)/110438, and checked that their normal residuals are orthogonal
to H K1 and H K2 respectively. H=diag(1,36,25) is invertible, so on either
Krylov subspace the quadratic objective has a unique minimizer. The columns of
[g,Hg,H²g] are independent, making K3 all of R³, and x3 has zero normal residual.
Thus the unique minimizer statements have the intended full optimization
meaning, and the exhibited pair is before termination and unambiguous.

## 3. Genuine Moore–Penrose projection

`augmentedMatrix` has rows indexed by `Fin m ⊕ Fin n` and is exactly
K=[A; ηI], η=‖r‖/‖x‖. It is not the mistaken horizontal concatenation of A and I.
`projectionError` forms the norm of KJ acting on the actual augmented vector
[r;0] and divides by ‖x‖.

The candidate J=(KᵀK)⁻¹Kᵀ is accompanied by an exported invertibility assertion
and **all four** Penrose equations. For nonzero x and r, η>0 and
KᵀK=AᵀA+η²I is positive definite, so the specification is true even for rank-
deficient A. The four equations characterize the genuine Moore–Penrose inverse
uniquely. Thus the draft is not replacing the pseudoinverse by an arbitrary
right inverse or by a definition containing the desired numeric result.

The separate projection-to-Gram theorem has the correct scaling. KJ is an
orthogonal projection, giving ‖KJv‖²=(Aᵀr)ᵀ(KᵀK)⁻¹(Aᵀr); multiplication of
KᵀK by ‖x‖² and division by that same squared norm yields exactly the draft's
matrix `‖x‖² AᵀA + ‖r‖² I`. If the normal residual is zero but r is nonzero,
both sides are zero, so the stated bridge still covers the canonical branch.
x=0 is outside all compared pairs.

## 4. Independent exact certificate reconstruction

`exact_check.py` uses only Python's `fractions.Fraction` and basic matrix
operations. It imports no author's checker or results. It reconstructs the
actual displayed data and equations directly. The rational checks passed:

- Full column rank, both Krylov membership identities, first/second normal-
  residual orthogonality, third Krylov basis independence and exact termination.
- Both displayed residual vectors and their exact normal-residual squared norms.
- The rational upper completion E, its strictly positive denominator, the full
  perturbed normal equations, and all three positive leading determinants of
  κI−EᵀE with κ=1979/2000. The matrix and determinants are retained in CHECKS.json.
- Both unit-direction quadratic values used in the informal upper proof.
- Every entry of `B−(99/100)I=K/2407881992100` and all four quoted positive
  principal determinants of the symmetric integer K.
- The zero-new-residual branch's exact inequality ‖r2‖²/‖x2‖²>99/100.
- Both very large exact rational projection-square values, all six positive
  diagonal inverse denominators, and the strict rational cutoffs
  `value1 < 503/500 < 1007/1000 < value2`.

The polynomial and rational checks are supplementary evidence of correct data
and statements. They do not certify Lean elaboration, kernel acceptance, or the
generic analytic bridges.

## 5. Universal lower bridge and complete negative conclusion

The lower-bound Challenge theorem quantifies over **every** feasible real 4-by-3
E, including rank-changing E and E giving zero new residual. This avoids the
common scope error of proving only the nonzero-new-residual branch.

For q=b−(A+E)x2 nonzero, u=q/‖q‖ satisfies (A+E)ᵀu=0 and
q=u(uᵀb). The genuine operator norm bounds both ‖Aᵀu‖ and ‖Ex2‖/‖x2‖ by ‖E‖.
The identity
`‖r−u(uᵀb)‖² = ‖r‖²−(uᵀr)²+(uᵀAx2)²`
gives the D quadratic form. The convex combination B and B−cI positive definite
then imply c<‖E‖². For q=0, Ex2=r gives the separately checked simpler ratio
bound. This specializes the informal general lemma without restricting the
actual perturbation set.

Attainment transfers the universal lower inequality to the actual minimum.
The upper feasible witness transfers its spectral bound to the first minimum.
Both errors are norms or minima of norms and hence nonnegative, allowing the
strict squared separations to imply strict unsquared increases. The final
`counterexample` statement includes the actual successive-iterate predicate and
**both** increases on the same pair. The two final universal negations are then
the full original negative resolution, rather than a certificate-only theorem.

## 6. Computation, reuse, attribution and remaining gates

All numeric data are rational, so exact LDL identities and positive rational
pivots can avoid interval subdivision and eigenvalue search. The draft preserves
the substantial generic obligations instead of assuming spectral norm bounds,
minimum attainment, or pseudoinverse identities as axioms. Its Comparator file
lists exactly the 17 declarations, permits only the three standard axioms, and
leaves `definition_names` empty. Definitions contain no placeholders; the 17
intentional `sorry` terms occur only in Challenge, with no Solution module yet.

Mathematical credit remains Matthew J. Colbrook, Cambridge DAMTP. Formalization
credit is George Stepaniants, Caltech Department of Computing and Mathematical
Sciences, with no George email. The draft correctly distinguishes this spectral
target from the cited paper's different Frobenius convention. The unchanged
canonical README, source record and final status will require review again at
publication.

The planned explicit LeanCert kernel mode and per-export `#assert_trust kernel`
must be implemented, and actual Linux type checks, full proof builds, transitive
axiom audit, default-kernel replay, sandboxed Comparator and negative controls
remain open. At least two independent final proof referees are still required.
This source-stage approval makes none of those later acceptance claims.
