# RA-02 statement review

**Approve for Linux statement elaboration.** The concrete definitions and all
27 contracts faithfully express the complete negative answer to the original
RA-02 question. This is a source review, not Lean execution, a statement freeze,
proof authorization, or whole-problem verification.

Reviewer: OpenAI Codex `/root`. I did not author either Lean statement file or
the numerical-first packet. I did propose the preceding finite arrowhead
mathematical route; that role is disclosed, and this is not an independent
rediscovery of that route. The separate nonauthor referee must assess the
statements independently. No human peer review or official Tau Ceti approval
is claimed.

The reviewed packet is bound by draft manifest
`10c1c64a95804f21dde488409bdda7affaa7f1d07b3d633b242314468db3cbb6`.
I read the whole canonical question, the whole contact-redacted 637-line
manuscript, numerical targets, every definition and Challenge declaration,
source correspondence, review plan, reuse notes, README, Comparator configuration,
and active metadata. A broad primary-source search was truncated; I then read
the relevant spectral and positivity definitions in bounded ranges and the
exact trace, exponential and real-power APIs. I do not claim to have reviewed
all proofs in every pinned library file. The companion script authenticates
bytes and records its actual static checks separately.

## Faithfulness and adversarial checks

`Square n` really uses complex matrices. Mathlib's PSD predicate includes
Hermitian symmetry and nonnegativity of the conjugate quadratic form, and the
explicit final hypothesis permits every PSD input, including zero and singular
ones. The two real constants are outside all dimension, matrix and rank
quantifiers. The rank range is exactly `1 <= r <= n`, the exponent is arbitrary
real `p >= 0`, and the expectation takes exactly `r` steps. The final negation
does not substitute a fixed-rank example or a lower-bound helper for that claim.

The sample space contains every function `Fin k -> Fin n`, converted to a
chronological list. Conditional masses use the actual current residual, not
the initial matrix and not independent draws. The rank-one update has the
original complex numerator and diagonal denominator. Returning the unchanged
matrix on zero diagonal is harmless because that event has zero mass at a
nonzero PSD residual. Uniform dummy labels after zero trace are harmless only
after the stated trace-zero equivalence and absorption have been proved. Both
are explicit obligations, as are all-step PSD preservation, nonnegative full
path weights, total mass one, extension identities and expectation recursion.
No new structure has assumed those mathematical facts as fields.

The eigenvalue definition uses `eigenvalues₀`, whose decreasing order is
actually proved in pinned Mathlib. The `Fin.cast` transports only cardinality;
it does not use the arbitrarily reindexed `eigenvalues` as an ordered list.
The tail includes zero-based indices at least `r`, matching the original
one-based indices greater than `r`. The contracts explicitly connect the list
to actual nonzero eigenvectors and trace, include PSD nonnegativity and the
empty rank-n tail, and identify the order-(r+1) tail with its least eigenvalue.
The Rayleigh quotient uses the conjugate quadratic form and the actual sum of
squared complex absolute values. The parameter `epsilon^r` is an upper bound
on a proved positive spectral tail, never a substitute definition of it.

The arrowhead family has the correct diagonal, cross terms and last diagonal.
Its stated quadratic identity is valid also at rank zero as an auxiliary
totalization; the counterexample itself uses rank at least one. A zero value
of the displayed positive weighted squares forces the last coordinate and then
all ordinary coordinates to vanish, so positive definiteness is a meaningful
nonvacuity obligation. The probe has last coordinate one and ordinary entries
minus alpha, giving exactly epsilon^r energy and norm squared at least one.

For a remaining ordinary set U, the second state is the Schur complement with
denominator c(U). Removing an ordinary label changes that denominator to
c(U\{i}); the stated pivot equals d_i c(U\{i})/c(U), which is positive. These
are the right formulas both before and after the distinguished pivot. The
update and all-distinct-history contracts require equality with the actual
process rather than using those formulas to redefine it. The terminal
pivot-product times trace equals epsilon^r times the product of the d_i,
and the probability-weighted version divides by the actual prefix traces.

The two retained choices at position s are distinct: the carry is either the
last label or less than s. The selected-prefix formula correctly includes s=0
and s=r; its erased carry yields the empty set initially and one survivor at
the end. Injectivity, cardinality 2^r, and no repeated labels are all conclusions
to prove. Every prefix trace bound refers to the chronological residual and
covers rank one. Nonnegative contributions outside the retained set remain
in the full expectation. The resulting sufficient factor 2^r/3 and positivity
of the actual tail imply strict violations for arbitrary real C,p by exponential
domination. The source's stronger sharp limit, entrywise positivity, correlation
examples and LU results are clearly excluded without narrowing RA-02 itself.

I checked zero residuals and diagonals, n=1, r=1, r=n, empty paths and sums,
repeated labels and zero-probability paths, complex vectors, the sorted-index
transport, and the order of the final quantifiers. I found no weakened target,
vacuous hypothesis, assumed desired conclusion, or missing semantic bridge.

## Computation, reuse, credit and remaining gates

The only planned numerical certificate is exp(1)<=3 in explicit LeanCert kernel
mode. Its future consumption in the final factor is required. Everything that
depends on rank remains symbolic: no enumeration of the binary tree, enormous
rational evaluation, approximate eigenvalues or interval subdivision is needed.
The pinned `Real.one_add_inv_pow_le_exp` and exponential-versus-real-power
theorem already provide the two standard analytic comparisons. The problem
contracts retain wrappers to expose the reviewed interface and their actual
consumers; the implementation should use those APIs rather than reprove them.

I applied the retained Tau Ceti correctness, generality, proof-quality, reuse
and attribution rubrics within this statement-only scope. Full library-wide
duplication search and proof-quality assessment of nonexistent proof bodies
are not claimed. Positive definiteness and final counterexamples provide the
required nontrivial future witnesses; they cannot be skipped at acceptance.
Colbrook retains the mathematical resolution credit. Stepaniants receives
formalization credit with the authorized Caltech department and affiliation,
and no contact email. The redacted manuscript is labelled as such rather than
represented as the original Git blob.

The metadata correctly says unchecked and unverified with no main results.
There is no Solution or proof body; only 27 intended Challenge placeholders.
Comparator names exactly all 27 contracts and permits no definition holes.
The dependency pins and numerical-first record are checked. A second
independent statement review, actual Linux elaboration, and an explicit frozen
boundary are required before implementation. Subsequent full source referees,
real Comparator, default-kernel replay, axiom and rejection/sandbox checks,
and an exact publication-commit rerun remain required before counting.
