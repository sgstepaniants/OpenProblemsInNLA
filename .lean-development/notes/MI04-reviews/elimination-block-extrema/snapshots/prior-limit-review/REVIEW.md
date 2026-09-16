# MI-04 independent incremental review: second-order limit

Reviewer: OpenAI Codex AI agent `/root/next_elimination`, independent of the
MI-04 implementation author. Review phase: mathematical source, under the
repository's scoped Tau Ceti fidelity, correctness, reuse and attribution
criteria. This is not human peer review or official Tau Ceti certification.

**Verdict: APPROVE the new limit module as source. No correction requested.**
Actual compilation of these new bytes is pending. This report does not approve
the full MI-04 proof or claim LeanCert, default-kernel or Comparator acceptance.

The handoff is `proof-handoffs/second-order-limit/MANIFEST.json`, SHA-256
`28d04bcc7b7b32a05b13147e5a7d5c4274c6fb89987c08550a901747a84a6509`.
The complete reviewed `NLA/MI04/Limit.lean` has SHA-256
`5a10598688c704f7ee2a13b990ee4cd9d35e2373ba051f651972a66e6aee6e1a`.
`INPUTS.json` and the retained snapshots bind the exact source, frozen boundary,
original mathematical source, handoff and primary Mathlib API files. All handoff
hashes match the current held package; all original-source hashes were also
compared to immutable Git revision `ce47b5630bf3680d9211131c3a43825b022c139a`.

## Scope and statement identity

I read the complete canonical MI-04 statement, integrated and original Colbrook
manuscripts, frozen Definitions, all Challenge contracts and numerical targets.
The canonical target is the universal positive-block Euclidean operator-norm
necessity implication for every positive finite dimension and arbitrary complex
off-diagonal block, including singular data. This new module supplies one
intermediate coefficient limit used in that argument; the remaining implications
and final assembly remain separate proof obligations.

The implemented `simple_peak_second_order` header matches its complete frozen
Challenge header after whitespace normalization, including all typeclass and
parameter context. It assumes a finite nonempty complex coordinate space,
`d a=1`, every other `d j≤1/2`, Hermitian `V`, and `V a a=0`. It concludes the
actual right-hand limit of
`(topValue (perturbedDiagonal d V ε)-1)/ε²` to `secondCoefficient d V a`.
It adds no eigenvector, differentiability, analyticity, convergence-rate,
invertibility or distinctness assumption. Other diagonal values may repeat and
may be arbitrarily negative. The one-coordinate case is included.

The frozen definitions use the real part of the actual complex quadratic form,
the genuine Euclidean operator norm through `Matrix.toEuclideanCLM`, and the
supremum over actual Euclidean unit vectors. None has been replaced by a matrix
entry norm or an assumed spectral value. The frozen sandwich header also matches
the implementation in `UpperBound.lean` exactly.

## Mathematical argument

`upperCoefficient_tendsto` treats each term of the actual finite sum. The peak
term is identically zero. For any other coordinate, `1-d j≥1/2`, so the limiting
denominator is nonzero. Its perturbed denominator
`1-d j-ε*spectralNorm V` tends to `1-d j`; division continuity therefore yields
the exact summand in `secondCoefficient`. Finite-sum continuity gives the full
coefficient limit, with no uniformity in a growing dimension asserted or needed.

`lowerCoefficient_tendsto` holds for fixed data without extra spectral
assumptions: the numerator tends to the fixed second coefficient and the
denominator `1+ε²*‖correctionVector‖²` tends to one. The proof supplies the
nonzero denominator limit explicitly. The correction vector is an actual finite
Euclidean vector, not a postulated eigenvector branch.

The main theorem proves `ε*(1+spectralNorm V)<1/4` eventually from convergence to
zero. Positivity of `ε` is eventual membership in the actual filter
`𝓝[>] (0 : ℝ)`. This is the standard nontrivial right neighborhood of real zero;
it is not an empty or custom limiting filter. The fixed finite norm means the
smallness condition is a genuine eventually true neighborhood for every `V`.
It imposes no new restriction on the eventual arbitrary matrix in MI-04.

On that neighborhood, the previously stated exact sandwich applies. Its lower
and upper functions both tend to the same coefficient. The pinned Mathlib
eventual squeeze theorem then gives precisely the frozen right-hand limit.
The proof correctly uses the eventual-inequality version; it does not require
the sandwich to hold at zero or at all positive parameters.

## Dependencies and source correspondence

I read `Coordinates`, `Correction`, `Punctured`, `UpperBound`, `Quadratic`,
`Rayleigh` and the consumed scalar inequality in `ScalarGeometry`, as well as
the new `Limit` module. The exact coordinate identities use complex conjugation
in the correct inner-product positions. The lower test vector is
`e_a+ε*correctionVector`; its true norm squared is `1+ε²‖w‖²`, and its quadratic
numerator is `1+ε²(‖w‖²+L)+ε³R`. The lower bound follows from actual Rayleigh
maximality after multiplication by the positive denominators.

The upper argument decomposes an arbitrary vector at coordinate `a`, bounds the
orthogonal remainder using the genuine operator norm, and applies the weighted
square inequality separately at every off-peak coordinate. Its perturbed gaps
are greater than `1/4` under the stated smallness hypothesis. Compactness and
normalization in `Rayleigh` connect those all-vector inequalities to the actual
supremum. The pointwise bounds are proved in the held source; they are not
assumptions introduced in `Limit` or the final problem's input predicate.

This is the documented variational replacement for the manuscript's simple-root
second-order expansion. It obtains exactly the coefficient needed to compare the
two block pencils under positive scaling. It does not advertise the manuscript's
stronger analytic expansion or a third-order error estimate. The narrower
auxiliary probe range `[-1/2,1/2]` in subsequent frozen contracts still includes
the zero and single-half probes required by the original argument.

The handoff's `Unitary.lean` hash is retained for provenance completeness, but
that file is not a dependency of `Limit` and was not re-reviewed in this bounded
incremental pass. Unrelated final normality, diagonalization, affine reconstruction
and whole-problem assembly are not approved by this report.

## API, trust and remaining evidence

Pinned Mathlib source at `0df444a360eaa60ab8c11dca51a86af692955474` was inspected for
finite-sum convergence, division continuity at nonzero denominator limits,
eventual strict inequalities, neighborhood membership, the nontrivial real
right-neighborhood filter and the eventual squeeze theorem. These APIs match the
mathematical use. No numerical interval subdivision is needed for this route.

The reviewed dependency source contains no proof holes, new axioms, unsafe/native
shortcuts or imports of Challenge. `Limit` selects kernel-only LeanCert trust and
contains both the export's axiom print and kernel trust assertion. Those commands
are prospective checks until this source actually executes. No local Lean/Lake
command was run and no package file was edited by this referee. Actual Linux
elaboration, measured transitive axioms, Comparator/default-kernel and operational
controls, final source reconciliation, and full-target independent reviews remain
required before any verification or publication claim.
