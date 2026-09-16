# IE-13 source correspondence — unapproved statement draft

The immutable source revision is
`ce47b5630bf3680d9211131c3a43825b022c139a`. The complete original target is
`linear-systems-and-elimination/IE-13/README.md`; the complete mathematical proof
is Matthew J. Colbrook's `references/colbrook-recovered-2026-09-11/manuscripts/IE-13.tex`.
Both, and the full dated independent informal review, are retained under
`source/` with exact Git/blob/SHA-256 identities in `SOURCE-PROVENANCE.json`.
The manuscript's original-source hash in its header and its later integrated
file hash are different identities; neither is silently substituted for the other.

The mathematical proof is credited to **Matthew J. Colbrook, Department of
Applied Mathematics and Theoretical Physics, University of Cambridge**. The
prospective formalization is credited to **George Stepaniants, Department of
Computing and Mathematical Sciences, California Institute of Technology,
Pasadena, California, USA**, with substantial AI assistance. No contact email
for George is supplied. Existing source attribution and historical qualifications
remain in the retained original files.

## Complete original target

The independent `sharp_growth` obligation ranges over every pair `p,q : ℕ`
with `p ≠ q`. Its set `growthValues p q` explicitly quantifies over every
`n ≥ 1 + max p q`, every actual nonsingular complex input with bandwidths at most
`p,q` in the given ordering, and every admissible maximal-modulus GEPP tie path.
No preliminary reordering is performed. The numerator of `growth` includes
every active entry at all `n` stages, including the input and final scalar. Its
denominator is the genuine maximum modulus of the original matrix.

`sharpConstant` is defined as the real `sSup` of that set, separately from the
proposed `sharpBound`. The main theorem asks for `IsGreatest` and the actual
supremum equality. A nonsingular rational witness and a legal complete path
must establish membership. Neither an empty path class nor a maximum defined
to be the answer can make the conclusion vacuous.

The bound is `1` for `p=0` and the real cast of `h_p(p+q)` otherwise. The source
recurrence has zero values at every nonpositive integer time and one plus the
previous `p` values at positive time. The draft's structural history register
implements exactly that proposed sequence, with separate `recurrence_history`
and `sequence_recurrence` obligations proving the correspondence. The source's
optional special closed forms and known equal-bandwidth comparison are not
required to establish the original unequal-pair question.

## All proposed exports

| Independent declarations | Source role and complete obligation |
| --- | --- |
| `gepp_model_semantics` | Explicit physical row swap and exact trailing Schur formula, starting from the original input. |
| `entryMax_semantics`, `activeMax_semantics`, `growth_semantics` | Actual attained finite maxima, positive nonsingular input scale and every active stage/entry. |
| `admissiblePath_exists`, `admissiblePrefix_extension` | Nonvacuous full GEPP paths and a proved extension of any genuine admissible prefix, with unchanged earlier entries and states. |
| `originalRow_update`, `multiplier_bounds` | Derive original-row-label updates from physical swaps and bound the actual complex Schur multipliers. |
| `front_structure`, `front_transition` | Prove the general lower-bandwidth front: at most `p` old rows, untouched future original labels, the actual chosen pivot in the front, and exact deletion transition. No front invariant is assumed. |
| `recurrence_history`, `sequence_recurrence`, `sequence_properties`, `envelope_recurrence` | Relate the structural recurrence to the source sequence, prove monotonicity/positivity and the exact envelope update at every time and coordinate, including `p=1` and the first update. |
| `late_column_zero` | Prove vanishing of old target values before the first permitted nonzero arrival. |
| `column_front_bound` | Bound every finite subset of actual surviving old rows by the canonical envelope at the correct column age. This replaces formal sorting while retaining every legal pivot choice. |
| `all_active_entries_bound`, `zero_lower_bandwidth`, `universal_growth` | Cover every entry of every active complex Schur matrix, the `p=0` exact-one case, and the dimension-independent upper bound. |
| `witness_scale`, `witness_structure` | Prove the exact rational scale, required dimension, original band support, input maximum one and rational-real entries of the literal construction. |
| `witness_prefix_order`, `witness_prefix_admissible` | The proposed current-row swaps induce the source's factor-row order and really are nonzero maximal-modulus GEPP pivots through the necessary prefix. |
| `witness_target_value`, `witness_nonsingular` | The actual active diagonal entry equals `h_p(p+q)` and the entire original matrix is nonsingular. Neither fact is a field of its definition. |
| `witness_attainment`, `identity_attainment`, `sharp_growth` | Construct complete admissible attaining paths, include every zero-bandwidth endpoint, and establish the least universal bound via the greatest actual value and its supremum. |

There are 28 deliberately unproved Challenge contracts. They are not 28 solved
problems. They all concern the single retained permanent problem IE-13.

## Indexing and witness correspondence

Source indices are one-based; all Lean indices are zero-based. The source order
`N=2p+q+1`, target column `J=p+q+1`, and scale `η=2^(-p)` become
`witnessOrder p q`, index `p+q`, and rational `witnessScale p=(1/2)^p`.
`witnessLowerRational` is exactly the source unit lower matrix with `-1` on its
first `p` subdiagonals. `witnessUpperColumn` uses the source first-column value
one, powers `2^(i-1)` at positive zero-based indices, and the subsequent basis
columns. `witnessFactorIndex` is the inverse of the source rotation
`(p+1,1,…,p,p+2,…)`. It assigns rows when defining the original input; it does
not change the initial GEPP state.

The full original matrix is explicitly defined over `ℚ` by finite matrix-vector
sums in early columns, the specified zero/one target column, and later identity
columns. `witnessMatrix` embeds these actual rational entries into `ℂ`.
`witnessSeedPath` picks current physical row `p` until that rotation is complete
and then picks the current diagonal row. Its prefix of length `p+q` is enough to
expose the target entry. The draft does not assume that its later choices are
valid: `admissiblePrefix_extension` must prove that an actual full path exists
and retains the entire preceding trajectory. The nonsingularity theorem is
separate, so it cannot be smuggled into that bridge through a witness predicate.

## Reuse and explicit semantics

The literal generic complex `rowSwap`, `schurStep`, `trajectory`, pivot predicates,
entry/active/growth maxima and `origin` recursion are copied from accepted IE14
proof revision `6e48f25fffdae2cf93e4985dc515abbd15e0481b` into this independent
namespace. `REUSE-AUDIT.json` binds their exact source blocks and confirms the
identical definition bodies. `gepp_model_semantics` additionally exposes the
original swap/update formula as an independent contract. No IE14 cyclic input,
two-row front, Fibonacci answer or proof theorem is imported.

After approval, generic IE14 GEPP and maximum proofs can be adapted at these
identical meanings. IE05's real scaled-LU code is an implementation reference
for factor cancellation, not a premise or a substitute for the present physical
swaps and arbitrary tie choices. Both prior implementations retain George's
formalization credit and their Apache-2.0 provenance.

## Computation reduction and required review

The proposed upper argument keeps bounds multiplied by the actual input maximum,
so a separate division/scaling argument is needed only at the final ratio. The
sorted-front proof can use sums over arbitrary finite subsets, with the exact
envelope sum explicitly defined and all subset inequalities left to prove.
Structural recurrence and finite symbolic algebra replace dimension enumeration,
root finding and interval boxes. A genuine kernel-only LeanCert rational bound
may support the scale; every eventual export must in any case pass LeanCert's
kernel trust assertions. No artificial interval certificate establishes the
all-parameter result.

The organization follows the pinned Schiffer/Forsythe statement/proof split and
the repository's scoped Tau Ceti review protocol. The two source-bound statement
approvals, actual Linux elaboration and immutable freeze are all pending. No
Solution or mathematical proof implementation exists. No actual LeanCert,
default-kernel, transitive-axiom or Comparator acceptance is claimed. Final
verification needs the complete proof graph and two independent nonimplementing
referees; the prior informal review and public duplicate audit are not substitutes.
