# MF-22 independent complete mathematical source review

**Verdict: APPROVE the complete mathematical source at the bound bytes. No
mathematical correction is requested.** This is a source review, conditional on
successful compilation of the entire graph and the separate canonical kernel,
Comparator, transitive-axiom and control gates. It does not establish Lean
verification, publication acceptance or an increase in the verified-problem count.
Any subsequent proof repair must be reconciled against this immutable snapshot.

Reviewer: OpenAI Codex agent `/root/next_inequalities`, an independent
non-implementing MF-22 referee. I wrote no MF-22 definition, statement or proof.
I am implementing the separate MI-04 problem and have reviewed other campaign
projects. The MF-22 author separately reviewed MI-04 source; neither such review
substitutes for the other project's actual compilation or the root referee.
I edited no author source and executed no local Lean, Lake, cache download, Git
mutation or workflow. This report applies the repository's scoped Tau Ceti
fidelity, correctness, completeness, proof-quality, reuse/API and attribution
criteria, not an official Tau Ceti service or external human review.

## Exact inputs and boundary

I read the original canonical MF-22 statement and complete retained manuscript,
every frozen definition and all 22 independent Challenge contracts, the numerical
dossier and source correspondence, all 29 active Lean source files, project and
Comparator configuration, all ten dependency pins, and the two original full
statement reviews and two notation addenda. `snapshot/` retains all these inputs;
`INPUTS.json` binds 52 files. The author's complete closure manifest is
`aee9f88bb62e832b0eade6aa456cbd98d4e8eeaccd802b4fbb7df81e154e1303`.
The review includes the three held repairs following development run 35043317938.
It does not claim that the final five modules or these repairs have compiled.

My reproducible source audit, `audit_source.py`, confirms that all 29 current
implementation files match both that manifest and this independent snapshot.
All ten frozen files remain byte-identical to the statement freeze. Both original
source files equal their actual Git objects at
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`. All 22 implementation signatures equal
their frozen Challenge signatures after removing comments and whitespace. Every
active module is reachable from `Solution`; no Challenge import, proof placeholder,
custom axiom, native-decision command or unsafe/foreign implementation occurs in
that closure. These are source checks, not a replacement for Lean elaboration or
a transitive kernel-axiom audit. `CHECKS.json` records the individual signatures,
pins and checks.

## Full target, definitions and norm conversion

The original problem is eventual polynomial conditioning for every fixed positive
real parameter. The implementation retains all eight literal coefficient blocks,
the integer row-minus-column offset, the original pure Toeplitz truncation and
all complex entries. The product index has exactly 2n coordinates. Its operator
norm is the actual complex Euclidean continuous-linear-map norm. The condition
number explicitly assigns infinity at determinant zero; the final theorem also
proves eventual nonzero determinant. Totalized inverse zero therefore cannot
make the result vacuous.

The source manuscript proves a linear estimate. The formal target deliberately
uses exponent two, which is sufficient for the entire original existential
polynomial question. Constants and the cutoff may depend on the fixed parameter,
but never on the running dimension. The final implementation obtains a uniform
entry bound for the true inverse and uses the proved cardinality-times-entry
operator-norm estimate for each of H and its inverse. With 2n indices this gives
`4 * (2 + rho) * B * n^2`, with a positive fixed constant. The conversion to real
power exponent two is exact. No claim to formalizing the manuscript's sharper
linear bound should be made in publication.

## Exact source recurrence and spectral classification

`Coordinates`, `SourceRows`, `LeadingBlock` and `SourceRecurrence` prove the
literal source equations after scaling by 80, not a substitute recurrence.
The leading-block determinant is 24 times the nonzero leading scalar, and the
transfer/forcing matrices use its actual inverse. The finite coordinate extension
and state `(u_j,v_(j-1),u_(j-1),v_(j-2))` recover the three left zeros and u_n=0.
The recurrence never adds an equation for v_n. It is equivalent to the full source
matrix equation for every right-hand side and every allowed row.

`TransferCertificates` identifies the actual 4-by-4 characteristic polynomial,
pencil determinant and adjugate entry by fixed-size exact algebra. `Coprime`
excludes a common complex numerator/denominator root for every positive parameter;
its real/imaginary elimination and positive-parameter contradiction have no
sampled-parameter premise. `ScalarCertificates`, `RootCubic`, `RootCayley` and
`Roots` prove the complete root classification. Negative discriminant is derived
from an exact positive quadratic and the positive parameter. In the ordinary
case, a real cubic root and a conjugate nonreal pair are obtained, and the Cayley
map sends their signs of imaginary part to the required inside/outside norm
classes. The pole is excluded by the actual polynomial evaluation.

The exceptional parameter rho squared equals 10 is treated separately. Its
quadratic has discriminant -14600; the missing Cayley root is -1, and the exact
quotient derivative there is nonzero. Together with the separate root 1 this
still gives four distinct nonzero roots. No final theorem assumes existence of
spectral data or excludes the degree-drop parameter.

## Projectors and the growing-mode cancellation

The spectral projectors are Lagrange polynomials evaluated at the actual transfer
matrix. `ProjectorPolynomial` proves the required nodal/characteristic divisibility;
`ProjectorAlgebra`, `EigenEvaluation` and `SpectralAlgebra` derive the complete
sum, orthogonality and every natural-power expansion by Cayley-Hamilton. The
zero-power case is included. These are not projectors supplied by an unproved
diagonalization premise.

`ProjectorRank` uses simple characteristic roots to bound the true eigenspaces,
then proves the full sandwich identity `Pi E00 Pi = gamma Pi` through dependent
columns and vanishing two-by-two minors. `Dominant` applies the actual singular
pencil adjugate and its eigenmatrix identities to show gamma nonzero: otherwise
the proved sandwich and trace relations force the forbidden adjugate entry to
vanish. This supplies both pieces required for Green cancellation; idempotence
alone is never substituted.

`ScalarTail` and `SpectralTailBounds` bound the three nondominant terms uniformly
in every natural power. They obtain a cutoff at least one, nonvanishing of the
actual scalar boundary, normalized-boundary norm at least one half, and an
inverse-normalization error bounded by a fixed constant times the inverse
outside-root power. Only fixed-parameter constants enter these estimates.

## Green reconstruction, inverse and all-index bounds

`GreenKernel` proves the exact forced one-step recurrence, initial-state form and
terminal first-coordinate zero. The natural subtraction in its first power is
protected by ell<j. `StateReconstruction` recovers every original coordinate,
including the terminal state needed for v_(n-1). `GreenInverse` proves a genuine
right inverse for the entire finite source matrix, derives the left inverse and
actual nonsingular inverse, and returns to H with the correct factor 80.

`GreenCoefficients` splits the two index ranges. If ell<j, cancellation uses the
exact exponent equality and the exponentially small normalization error to
bound the apparently growing term. Otherwise the combined exponent is at most
n, giving a fixed bound. Cross terms likewise use only powers with exponent at
most n. `GreenEntryAlgebra` expands the literal Green matrix using the full
rank-one sandwich. `GreenEntryBounds` bounds all five resulting terms by
fixed-dimensional four-entry sums and a positive majorant. It then discharges
root existence, gamma nonzero, all spectral hypotheses and the cutoff for every
positive parameter. The conclusion includes every n beyond the cutoff, every
0<=j<=n and every 0<=ell<n, with all four state and two forcing coordinates.
`Conditioning` uses exactly these entries to bound every entry of the true H
inverse. No finite size experiment, omitted boundary or surrogate inverse is
used in the universal result.

## Efficiency, reuse, credit and remaining gates

The reduction appropriately avoids numerical roots, interval subdivision,
growing-size determinants and unnecessarily sharp norm estimates. Only exact
small-matrix polynomial algebra is computational; the all-parameter and
all-dimension work is symbolic. The pinned Mathlib cubic, Lagrange,
Cayley-Hamilton, eigenspace, nonsingular-inverse and Euclidean-operator APIs are
used for their actual objects. The final source includes genuine LeanCert
kernel-trust and axiom-print commands for every one of the 22 exports. Comparator
has the same 22 targets, no definition holes and only `propext`,
`Classical.choice`, `Quot.sound` in its permitted list. Actual execution remains
necessary to establish those properties transitively.

Original family/question/classification credit remains with Bogoya, Böttcher,
Ferrari, Grudsky and Serra-Capizzano. George Stepaniants receives the retained
manuscript and formalization credit, Department of Computing and Mathematical
Sciences, California Institute of Technology, without an email address. AI
assistance, Schiffer/Forsythe structural examples and tool/library credit are
disclosed. The preserved draft metadata and frozen `defaultTargets = Challenge`
accurately record historical provenance but must be updated through an explicit
publication tooling/metadata transition after actual acceptance; this source
review does not promote them or change the mathematical boundary.

The complete proof graph must now compile at these bytes (or reviewed repairs),
then pass the actual isolated canonical Comparator, default-kernel replay,
permitted-axiom audit and rejection/sandbox controls. Both independent final
referees must reconcile the resulting raw evidence and final source identities.
Until then, this is mathematical source approval only.
