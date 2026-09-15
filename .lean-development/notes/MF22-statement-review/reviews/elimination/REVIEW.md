# MF-22 independent complete statement review

Reviewer: OpenAI Codex agent `/root/next_elimination`, 15 September 2026.
I am an independent non-implementing referee for MF-22. I edited none of its
statement or author files and ran no local Lean, Lake, dependency/cache download,
workflow or Git mutation. The held draft and original sources were copied for
this review; `INPUTS.json` and `CHECKS.json` bind the exact inspected bytes.

**Verdict: APPROVE the complete mathematical statement boundary. No mathematical
correction is requested.** This is not Lean elaboration, proof acceptance,
canonical Comparator verification or authorization to skip the remaining gates.

## Original target and the permitted exponent change

I read the complete canonical README and retained solution, including all four
sections, the exceptional parameter and finite Green-matrix estimate. Their
bytes match immutable upstream 8f04b905 and remain identical at the inspected
ce47b563 revision. The original problem asks for some nonnegative polynomial
exponent for each fixed positive real parameter, with constants independent of
the running dimension. It does not require exponent one. The proposed exponent
two therefore proves the complete original target, while not certifying the
source's stronger linear estimate. This distinction is stated explicitly in the
numerical targets, metadata, source correspondence and final two declarations.
It must remain explicit in eventual publication documentation.

I read Definitions, every one of the 22 Challenge contracts, the full numerical
boundary, source mapping, metadata and Comparator configuration. The final
`polynomial_conditioning` theorem retains every positive real rho, a fixed
positive constant and nonnegative real exponent, one natural cutoff at least
one, every larger natural size, actual determinant nonzero and the genuine
condition-number bound. No spectral datum or inverse certificate is an extra
hypothesis of this final theorem.

## Definitions, norms and actual source equations

The eight coefficient arrays and their rational prefactors are literal copies
of the canonical statement. The matrix is indexed by `Fin n × Fin 2`, with the
first coordinate the block index and genuine integer subtraction for the
Toeplitz offset. No corner correction or row/column permutation is introduced.
The positive dimension used by the eventual target is exactly 2n.

`spectralNorm` is the norm of the actual complex Euclidean-space operator
`Matrix.toEuclideanCLM`, whose pinned Mathlib definition and action on vectors
I inspected. `conditionNumber` explicitly assigns infinity when the determinant
is zero, avoiding the totalized-inverse trap. The remaining branch uses the
product of the actual matrix and actual inverse norms. The general entry-norm
bound has the correct dimension factor; it also makes sense for the empty
index type, where both sides vanish. The original target uses n at least one.

I checked the actual two block equations after scaling by 80: all six complex
coefficients and the 96i and 24rho terms match. The leading block and forcing
matrix use its genuine inverse. `source_recurrence` is an equivalence for every
actual vector and right-hand side. Finite zero extension supplies the three
left boundary zeros and u_n=0. Although the helper is zero outside the finite
vector, v_n never occurs in the required recurrence or states through j=n, so
it imposes no additional condition on the original problem. The final v_(n-1)
is recovered from state n, as required.

## Spectral and polynomial obligations

The numerator, denominator, reciprocal quartic, quotient cubic and real Cayley
cubic have the source coefficients and signs. The fixed-size determinant,
adjugate and characteristic-polynomial identities are obligations about the
actual T, and may replace the source's generating-function inference without
weakening the target. The no-cancellation statement covers every complex root
and every positive real parameter.

The real-cubic discriminant agrees with Mathlib's actual discriminant convention.
The positive quadratic is asserted on all real arguments. The Cayley identity
is complex, with the correct nonzero denominator hypothesis, and the inverse
pole is separately excluded. The degree-drop case rho²=10 has the correct
quadratic discriminant -14600 and simple quotient root -1. No eventual theorem
excludes this parameter.

`RootData` asserts four distinct nonzero actual quartic roots, ordered as 1,
another unit-modulus root, an inside root and an outside root. Its existence for
every positive parameter is an unconditional exported goal, so the later
conditional spectral lemmas do not hide a missing root classification. Since
the quartic has nonzero leading coefficient and degree four, this is the full
root set. The Lagrange basis is evaluated at the actual transfer matrix. I
inspected the pinned basis and evaluation conventions. The draft requires the
complete projector sum/product and all-power identities, not a named abstract
diagonalization supplied as a premise.

The dominant-projector obligation includes both gamma nonzero and the full
matrix identity Pi E00 Pi = gamma Pi. That identity is stronger than idempotence
and is precisely what the Green-matrix cancellation needs. Uniform remainder
and denominator bounds have constants independent of every running index, and
they quantify over every natural power. Root-dependent constants are harmless
because the later unconditional theorem chooses a root datum for the fixed rho.

## Green matrix, true inverse and final polynomial bound

The first Green power uses natural subtraction only under ell<j; the second
uses ell<n. All intended indices 0<=j<=n and 0<=ell<n are present, including
j=0 and j=n. The scalar boundary inverse multiplies the matrix product in the
correct order. Reconstructed u-coordinates use state j and v-coordinates state
j+1. `green_source_state` and `green_inverse` explicitly require these formulas
to be the states of the genuine inverse application and a two-sided inverse of
80H. They also require H nonsingular and H inverse = 80Q, so no surrogate inverse
or missing scaling factor can satisfy the final result accidentally.

The uniform kernel-entry theorem is unconditional in rho>0 and ranges over all
sufficiently large sizes and every allowed finite index. It therefore must
actually discharge root existence and the growing-mode cancellation. It yields
a uniform bound for every true inverse entry. The original entries have the
valid loose bound 2+rho. Applying the genuine operator-norm estimate to both
2n-by-2n matrices gives 4(2+rho)B n², with a positive constant fixed in n.
Converting n² to real power exponent two gives the complete final target.

## Independent diagnostics and scoped review

The small independent Python checker uses exact rational complex arithmetic,
not floating point. It verifies the full discriminant and completed-square
coefficient identities; 35 fixed determinant/cofactor/characteristic polynomial
points; 30 complex Cayley points; five coprimality-elimination data sets; and
25 actual finite Toeplitz/Green inverse instances, with 2800 endpoint-inclusive
state-entry identities. These diagnostics passed. They supplement the full
mathematical statement review and are not universal proofs or Lean certificates.
I did not rely on the author's diagnostic script to form this verdict.

The implementation plan minimizes computation appropriately: fixed 2-by-2 and
4-by-4 polynomial identities, exact completed squares and symbolic finite sums
replace parameter subdivisions, numerical roots, or determinants growing in n.
The difficult four-root classification, spectral projection and uniform
Green-kernel bounds remain explicit proof obligations. Prior MF-12/MF-24 norm
patterns may be useful, but extending real statements to complex matrices still
requires an actual proof; no such result is imported as an unproved premise.

Original manuscript and formalization credit are correctly George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology. Original family/question/source-root-classification credit remains
with Bogoya, Böttcher, Ferrari, Grudsky and Serra-Capizzano. No George email is
published. Schiffer/Forsythe structure, LeanCert kernel-only gates, standard
transitive-axiom allowance, empty Comparator definition-hole list and truthful
v0.4 metadata are present. The actual schema validates; all 22 configured targets
match the independent Challenge. Deliberate placeholders occur only there.

This is an AI-agent review under the repository's scoped Tau Ceti fidelity,
correctness, completeness, reuse, API and attribution criteria. It is not
external human peer review or official certification. A second independent
statement review, actual non-root Linux elaboration and an immutable freeze
must precede proof implementation. Complete proof development and all canonical
kernel/Comparator/control and final referee gates remain pending.
