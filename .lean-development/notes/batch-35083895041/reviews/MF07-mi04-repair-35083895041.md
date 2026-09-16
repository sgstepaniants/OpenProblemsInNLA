# MF-07 independent source continuation after run 35083895041

**Approve the exact proposed repair for an actual Linux rerun. No successful
compilation, Comparator result, or complete problem verification is claimed.**

Reviewer: `/root/mi04_independent_referee`, a nonimplementing reviewer of MF-07.
The implementing agent is `/root/mf22_publication_referee`. My separate
authorship of a MI-04 repair does not make me an author of this MF-07 change.
I did not edit MF-07 sources, execute Lean/Lake, change Git, publish, or change
the accepted count.

The reviewed author manifest is
`c5395fa308a4ccd5551e06d3c5dc6ddbbbfcaa95a0f372fb89a4f626ec3de9cc`;
the complete twenty-source candidate closure is
`6f12c614f2354af566c35b9bd318f931caa783e26be106426e5c7b3912688db6`.
This report continues my earlier complete twenty-file mathematical review
and its unitary-wrapper addendum. The intervening four-file repair has its
own independent review by `/root/ie13_continuation`; I re-read its full patch
and review and rehashed the sealed packet. I do not relabel that other
agent's full-file reads as mine.

For the current repair I read both complete replacement modules, their entire
patch, frozen Definitions, all eighteen Challenge statements, numerical
obligations, the original canonical target, and the corresponding manuscript
maximal-determinant argument. I read all 211 lines of the actual MF-07 module
log and all eighteen Challenge log lines, plus the relevant primary API
declarations and surrounding definitions.

## Exact source and mathematical assessment

Only `ScalarFamily.lean` and `Auerbach.lean` change, within four existing
declaration bodies. The other eighteen sources remain byte-identical. There
are 187 unchanged declaration headers when the two abbreviations are counted;
the author's count of 185 excludes those two abbreviations. All eighteen
exported signatures match the frozen Challenge, allowing only the same
qualified-name and grouped-existential syntax normalizations established in
the previous complete review. The complete import graph from `Final` still
contains exactly twenty modules.

In `scalar_growth_eq`, the length proof is now supplied directly as
`List.length_replicate`. Its two parameters are implicit in the inspected
Lean 4.33.1 source and are fixed by the existing length goal. The actual
compiler diagnostic independently exhibits that proof type. The maximizing
scalar is still obtained by compact attainment and repeated exactly n times;
the empty word, zero norm, and n=0 cases are retained. No numerical search,
finite-cardinality restriction, or new helper assumption is introduced.

The coordinate expansion replaces the nonexistent `PiLp.sum_apply` with the
actual `WithLp.ofLp_sum`, `Finset.sum_apply` and `PiLp.smul_apply` APIs. The
pinned definition of PiLp is a WithLp synonym whose function coercion is
`ofLp`. Thus these projections give precisely the same coordinate sum of
scaled columns, with ordinary complex commutativity matching matrix-vector
multiplication. They do not replace the Euclidean norm by a Pi norm.

The compact determinant maximizer is unchanged. Its column-membership proof
now unfolds the selected matrix, rewrites the already-proved column identity,
and directly uses the chosen column's subtype property. This avoids the
observed over-simplification of that premise to `True`. The actual norm-unit
ball, compactness proof, scaled coordinate-basis witness, nonzero determinant,
and maximization property all retain their existing meanings and hypotheses.

The three local-let repairs in `maximal_basis_coordinate_bound` use
`dsimp only` before the existing rewrites. This is appropriate for the actual
errors in which `rw` was given vector or matrix values instead of equalities.
The determinant identity still follows from scaling and replacing one column.
In the nonzero branch, nonnegativity and `v y ≠ 0` still prove `0 < v y` before
normalization. The zero branch still derives y=0 and then z=0 from the proved
invertibility of T. The final simplification adds only associativity and
commutativity to align the same real factors before canceling the strictly
positive factor `‖T.det‖`. No zero denominator is silently canceled.

The constructed coordinate matrix, rather than the original arbitrary matrix
generators, is required to be invertible. Empty-dimensional helper statements
and the scalar final endpoint are unchanged. No simplicity, distinctness,
nonzero generator, irreducibility, or finite-family assumption is added.
The original quantifier order remains a dimension-only constant followed by
every nonempty compact complex family of radius one and every positive-length
word. These changes do not affect the later ordered singular-coordinate,
rounding, damping, or quantitative comparison arguments.

## Actual evidence, safeguards, and limits

The failed before-source run is **35083895041**, literal commit
`09f9c4fd10c6e7d1efdb60eb0f43bc33ed920833`, job **104754071378**, nonroot UID
1001. I independently compared all twenty before sources, the Complete
wrapper and frozen Challenge with literal Git, the receipt and every one of
its thirteen post-command maps. Both complete MF-07 artifact logs match the
timestamp-stripped raw job log exactly and in order. Root actually executed
the separately retained 1,897-input operational audit; I did not rerun or
relabel that audit as mine.

ScalarFamily and Auerbach failed. Definitions, MatrixBasics, Numerical,
CompactGrowth, ProductEnvelope, RootSemantics, UnitaryGeometry, Interspersed,
NormGeometry, ApproximateNorm and TriangularDamping built. The unchanged
Numerical module built in 3.9 seconds and printed only the three permitted
foundational axioms for all four reported numerical declarations. Its
LeanCert exponential certificate and symbolic downstream consumption remain
unchanged. This is component evidence, not complete MF-07 acceptance.
The failed modules' `sorryAx` dependencies were explicitly rejected by the
existing trust assertions. The eighteen deliberate Challenge holes are
specifications. No Comparator ran in this development workflow.

All ten frozen inputs, checker/dependency pins, source imports, options,
trust assertions and resource limits are preserved. Static inspection found
no new axiom, hole, native shortcut, unsafe declaration, Challenge import or
hidden section assumption. Five primary Mathlib files were checked against
their exact Git objects at `0df444a360eaa60ab8c11dca51a86af692955474`.
The core List source was matched to the installed 4.33.1 file; no fresh core
Git-membership verification is claimed.

The prior complete review's scoped Tau Ceti generality, correctness, reuse,
trust and attribution requirements continue to apply. Colbrook retains
mathematical authorship at Cambridge DAMTP; George Stepaniants retains
formalization credit, Department of Computing and Mathematical Sciences,
California Institute of Technology, with substantial AI assistance. The
license is unchanged and this report adds no email or priority claim.

The independent Python audit initially stopped on lexical `/tmp` versus
`/private/tmp` path spelling. Its guard was corrected to compare the resolved
paths, while retaining the original path strings and the initial failed
script. The complete audit then passed. No author or proof source was changed.

There is no outstanding source correction request from this review. A fresh
unchanged-checker Linux build, complete default-kernel and standard-axiom
checks, Comparator and rejection/isolation controls, and canonical published
commit evidence remain necessary. This report authorizes no count increase.

All manifest keys are relative to this review directory. External `../..`
bindings deliberately identify the existing immutable packets and raw run
evidence; they are not claims that those files were newly generated here.
