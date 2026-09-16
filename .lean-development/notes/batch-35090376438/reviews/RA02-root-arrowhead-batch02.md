# RA-02 arrowhead prefix: root source review

Approve the mathematics of the exact four new modules (432 lines) for a future
Linux development build. The StateConstruction conditional has a predictable
elaboration concern matching the first-batch compiler failure; integrate it
only with a separately reviewed amendment or retain its original failure risk.
This source approval is not a successful build or a full RA-02 verification.

Reviewer `/root` did not author these Lean statements or proof bodies. I earlier
proposed the finite arrowhead strategy at a mathematical planning level; that
role is disclosed. I read all four new modules, frozen Definitions and all 27
contracts, the preimplementation plan, author notes and complete nonauthor
MI04 referee report. The seven predecessor sources were read in my retained
foundation review; their hashes and frozen source boundaries are rechecked here.

Literal true/false state entries follow the fixed finite label embedding.
Ordinary labels exclude the distinguished last label. The corner stays positive
even for an empty active set; erasure removes exactly one positive weighted
square. This gives the stated false-state diagonal with a justified nonzero
denominator. Complex Hermitian symmetry is explicitly proved.

The actual complex matrix quadratic form is expanded before identification
with the real sum of weighted squared complex moduli. Thus stateEnergy does
not replace the genuine quadratic form by definition. Nonnegative weights
give PSD for every active set. In the full set, either a nonzero last coordinate
or a nonzero ordinary coordinate supplies a strictly positive summand. This
proves actual positive definiteness, including all dimensions in the public
contract. Empty sums and the helper rank-zero case are handled by the last term.

The false state is identified with the actual distinguished Cholesky update
using its positive corner and proved pivot row/column cancellation. Its PSD
then follows from the genuine congruence theorem. The erasure formula supplies
positive active diagonals. The Rayleigh probe is nonzero at the last coordinate,
cancels every ordinary square and has the exact positive Euclidean squared
norm claimed. These are four exact frozen contracts. No eigenvalue-tail theorem,
normalization assumption or final probability bound is inferred from them.

The original target still concerns all complex PSD matrices, exactly r pivots,
all histories and arbitrary real exponents. Ten of 27 contracts have source
implementations; 17 remain. Using a real positive-definite witness family is
valid for disproving that full universal complex statement.

I independently authenticated all thirteen cited Mathlib files against literal
pinned Git blobs and inspected the complex norm/order, finite-sum and actual
PSD/PD APIs. The core Fin snapshot is only the installed pinned-version source,
not newly authenticated remote core Git. The author's regex-generated HEADERS
record combines equation-style pathResidual/pathWeight text; I do not rely on
that heuristic for definition fidelity. Definitions are immutable bytes read
directly, and each public theorem header was independently matched exactly.

The actual 35090376438 first-prefix build failed in PivotAlgebra. Its proposed
repair and the later StateConstruction follow-through are separate scopes.
No failed declaration or unexecuted trust print is accepted as proof here.
No new LeanCert intervals, determinant enumeration, eigensolver, rank expansion
or increased resource allowance is introduced. Applicable Tau Ceti fidelity,
nonvacuity, reuse and efficiency standards were reviewed manually, not by an
official CLI. Attribution, Caltech department affiliation, Apache licensing and
the no-email requirement remain intact. Complete independent final reviews and
actual kernel/Comparator/control/publication checks are still required.
