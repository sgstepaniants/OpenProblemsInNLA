# IE-13 root independent statement review

**APPROVE the complete proposed mathematical boundary, with no requested
correction.** Reviewer: OpenAI Codex agent `/root`, independent of the IE-13
author and nonimplementing. This approves the exact definitions and 28 contracts
in draft manifest `7df9990e5e5f944f4c90890a6e12cd0cc6b9838cbbde2ee33a9f5061d7516c38`.
It is source approval, not statement elaboration or completed verification.

I read the complete canonical README, entire mathematical manuscript, numerical
targets, literal Definitions, all 28 Challenge contracts, source correspondence,
metadata and retained earlier informal review. I then read the separate current
matrix-functions statement report. The previous PASS labels were not premises
of my mathematical assessment. All three original documents were compared to
their immutable Git blobs. The 21 draft hashes and all thirteen reused generic
definition bodies were checked directly, not inferred from an author's report.

## Target, actual algorithm and extrema

The final contract uses every unequal natural bandwidth pair and the actual
union over dimensions at least `1 + max p q`. Inputs are nonsingular complex
matrices satisfying the given-order bandwidth inequalities. Every active
nonzero maximum-modulus pivot is allowed; no tie rule or initial reordering is
imposed. `trajectory` starts at the original matrix, performs the current
physical row swap and subtracts the actual complex Schur multiplier. Padding
outside the next active block does not remove any entry of that active block.
The explicit `gepp_model_semantics` contract states this formula again.

The NNReal finite suprema use the genuine complex modulus. `growth` includes the
input and all later active stages through the final scalar. The maximum
semantics require both bounds and attainment, and positive input scale follows
from nonsingularity in a positive dimension. The stronger growth bookkeeping
for any path is valid because even a nonadmissible path defines a finite
trajectory containing stage zero; later growth bounds still require the full
legal-path predicate. Separate full-path existence and prefix-extension
contracts prevent a vacuous statement or assumed successful witness path.

`growthValues` contains actual realized growth ratios, not conditional proof
certificates. `sharpConstant` is the real supremum of this set independently of
`sharpBound`. The final greatest-element assertion requires an actual realizing
matrix and path. Thus the exact witness plus the universal bound prove the
original least dimension-independent upper bound and its supremum equality.

## Recurrence, provenance and full upper bound

The history register uses structural recursion in time. Its zero initialization
and shift at positive slots give the source values at all nonpositive indices
as zero. `recurrence_history` and `sequence_recurrence` expose the required
correspondence; no recurrence theorem is assumed. Monotonicity and positivity
include p=0. For positive p the envelope has a separately defined zero state,
an all-ones first state, decreasing coordinate order and the correct update.
The p=1 endpoint has no middle coordinate, and its final-coordinate update is
correctly still one plus the previous first value.

Original row labels are carried by the actual composed swaps. At stage k,
original labels at least k+p have zeros in all previously eliminated columns,
so they cannot have been earlier nonzero pivots and retain their original
active entries. The previous k pivots came from smaller labels, leaving at
most p old survivors. The chosen pivot belongs to those survivors plus the
fresh original row when it exists. The next old set is exactly that front
with its actual pivot deleted. Bottom truncation merely removes absent rows;
it requires no assumption about the front being full. The contracts assert
these invariants as conclusions for every legal path.

The subset-sum envelope retains enough information for arbitrary pivot choices.
For r>=1 surviving rows, triangle inequalities give their original magnitudes
plus r times the pivot magnitude. This is bounded by the largest r+1 front sum
plus (r-1) times its largest value. All subset-cardinality inequalities therefore
propagate to the stated envelope after appending a fresh value bounded by the
input scale. The zero-envelope first update is treated separately; subsequent
envelope entries are at least that fresh bound. This reasoning uses moduli
only and does not force GEPP to pivot on the target column.

For an early target column j<p+q, the initial all-ones state is one imaginary
update and its stage-k age is k+1<=j+1<=p+q. For a late column, old target
entries remain zero through stage j-(p+q); the first nonzero fresh arrival can
then contribute one update per following stage. `columnAge` is exactly this
truncated difference. The inclusive endpoint of `late_column_zero` is correct.
The general bound covers all active rows and columns, including untouched
original rows and selected pivot rows. For p=0 the original matrix is upper
triangular, nonsingularity gives nonzero diagonal pivots, and all lower
multipliers vanish. Its growth and the identity witness are exactly one.

## Original-order rational witness and endpoints

I translated the full construction independently: order 2p+q+1, target column
p+q, scale (1/2)^p, unit lower factor with the first p subdiagonals minus one,
the early powers-of-two vectors, and later identity columns. The factor-label
map is the inverse rotation of the source. It is used to define the original
matrix, not to pre-permute GEPP. Early geometric cancellations put support in
original rows k through k+p and leave magnitude at most 2^p before scaling.
The target column starts at original row p, q positions above its diagonal,
and ends p positions below it. These facts give the literal band condition,
rational-real entries, and initial maximum exactly one.

Choosing physical row p during the first p steps realizes the source rotation;
the subsequent choice at index p is an identity swap. Thus q=0 already completes
the necessary rotation after exactly p steps; p=0 gives the identity rotation.
The early nonzero factor pivots have competing multipliers of modulus at most
one. Prefix admissibility is consequently the right mathematical obligation,
including ties, and no later seed choice is assumed valid. The target-column
forward recurrence has initial data one, then p zeros, then ones; its next
values are exactly the proposed h-sequence. The active target diagonal equals
h_p(p+q). Nonzero leading pivots and the later identity block establish the
whole matrix's nonsingularity, asserted separately. A proved prefix extension
retains that visible attaining entry in a complete legal trajectory.

The target dimension bound holds for all p,q. The witness covers q=0 and p=1;
the identity covers p=0. Equal pairs are allowed in stronger helpers but the
final theorem preserves the canonical unequal-pair scope. Optional special
closed forms are unnecessary for the original question. No finite parameter
cap, hidden invertibility assumption, real-only upper bound or changed norm is
present.

## Structure, standards and remaining gates

I applied the repository's pinned scoped Tau Ceti protocol for fidelity,
generality, correctness of the planned reductions, API reuse, documentation
and attribution. The accepted IE14 generic GEPP/maxima/origin bodies are copied
exactly; no cyclic-band or two-row result is imported. Pinned Mathlib finite
supremum and real-LUB APIs support the chosen meanings. Structural recurrence
and finite-subset algebra avoid interval subdivision or enumeration in Lean.
The original mathematics remains Colbrook's, Cambridge DAMTP; George
Stepaniants receives formalization credit with Caltech's Department of Computing
and Mathematical Sciences and no personal email. AI assistance is disclosed.

I actually validated the draft YAML with the pinned v0.4 schema and compared all
28 ordered declarations with Comparator's configuration, including its empty
definition-hole list and three permitted standard axioms. All ten dependency
revisions and the Lean toolchain match the accepted campaign pins. Configuration
and license identities were checked; this does not claim a separate legal
review or reading of every line of every retained dependency file.

The author package currently contains only Definitions and 28 deliberate
Challenge placeholders, not an implementation. I ran no local Lean/Lake and
made no author-source edit. Source approval must be followed by actual Linux
statement elaboration and an immutable freeze before implementation. The future
complete proof needs two independent final mathematical reviews plus actual
non-root Linux Comparator, default-kernel, transitive-axiom and rejection/sandbox
controls. Neither this report nor bounded informal diagnostics count as a
Lean-verified problem or an official Tau Ceti endorsement.
