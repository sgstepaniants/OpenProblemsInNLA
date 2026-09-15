# IE-17 second independent statement review

**APPROVE the corrected complete mathematical statement boundary.**

Reviewer: `/root`, an AI agent, independent of both statement authors. Date: 2026-09-15.
This is a mathematical statement review following the repository's scoped Tau Ceti protocol.
It is not human peer review, proof-code approval, or a mathematical verification claim.
`exact_reconstruction.py` and `EXACT-CHECKS.json` retain independent exact supplements.
The script uses only rational arithmetic and coefficient identities; it is not a Lean certificate.

I read the full retained canonical README and complete Colbrook manuscript at
8f04b905eb2e0827b6b84f37d9d080ae1f05b202. I compared every definition, all 17
Challenge signatures, the numerical targets and explicit data against those
sources. This is the canonical spectral-norm target, not the distinct source
paper's default Frobenius norm convention. Both original monotonicity claims
are negated with the same successive nonzero full-column-rank witness.

The vector norm is genuinely Euclidean and Matrix.Norms.L2Operator fixes the
matrix norm. All perturbations of A with b fixed are allowed, including rank
changes and zero new residuals. The error is the actual infimum of their norms;
its least-element contract requires true attainment on a closed finite-dimensional
feasible set. This closes the strict-infimum gap. The exact-solution zero case is
explicitly included. No admissible perturbation is excluded to simplify the bound.

IsLSMRIterate states membership and full universal normal-residual minimization
on the actual Krylov span, with the source's minimum-length tie convention. The
witness equivalences prove unique minimizers rather than membership or comparison
with only finitely many candidates. The source itself supplies this optimization
specification as the definition, so a floating-point algorithm bridge is not
needed. The chosen first/second pair is nonzero and nonterminated; the third is
an exact solution. The universal propositions impose no hidden rank hypothesis.

The approximation retains the augmented projection and actual Euclidean norm.
Its Gram formula must satisfy all four Penrose identities with invertibility;
the efficient scalar formula is a separate theorem obligation, never the meaning
of the approximation by declaration. The zero-at-solution convention is handled,
including nonzero least-squares residuals. The corrected explicit Matrix.mulVec
syntax expresses precisely the intended inverse Gram quadratic form. The earlier
newline-dot syntax failed actual elaboration; its failure remains in the record.
The correction changes no mathematical definition, hypothesis or target.

I independently rebuilt all literal matrices with Fraction arithmetic, checked
the rank minor, Krylov orthogonality, rational feasible completion, positive LDL
certificates for the upper and lower matrices, the nonzero denominator, the
zero-new-residual ratio and both exact projected squared fractions. These are
supplements to the source review. The proof still must establish the real
operator-norm bridges, the all-feasible-perturbations argument, norm nonnegativity
and minimum attainment. For a nonzero new residual q, its unit direction obeys
q=uu^T b and both Rayleigh bounds; the q=0 branch uses Ex=r directly. Neither
branch can be omitted. Squared inequalities are converted only for nonnegative
actual norms/errors.

All 17 obligations are mathematically sound and cover the full retained target.
George's formalization credit and Caltech CMS affiliation omit his email, while
Colbrook's mathematical authorship is preserved. The corrected Challenge still
requires an actual successful Linux elaboration rerun before proof begins.
No statement freeze or proof-start authorization for IE-17 is asserted here.
