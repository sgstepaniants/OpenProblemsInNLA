# IE-13 numerical and mathematical targets

**Statement draft; unapproved and unfrozen.** The associated Definitions and
Challenge must be independently reviewed and actually elaborated before proofs. The original statement
and complete proof at upstream `ce47b5630bf3680d9211131c3a43825b022c139a`
govern all definitions. Optional source closed forms are excluded from the
minimum complete target.

## Literal domains, algorithm and maximum

- Parameters are natural numbers `p,q`; the original question requires `p ≠ q`.
  Both zero-bandwidth edges must be retained. A proof for all pairs is allowed as
  a stronger result, but not required.
- Dimensions are arbitrary natural `n ≥ 1 + max p q`, hence positive. Matrices
  have entries in `ℂ`. Nonsingularity is `A.det ≠ 0`.
- Zero-based bandwidth means `A i j = 0` whenever `j.val+p < i.val` or
  `i.val+q < j.val`. It is a condition in the original input ordering.
- A pivot path is a function `Fin n → Fin n`. At step `k`, the chosen row lies
  in the active rows, its column-`k` entry is nonzero, and its modulus is at
  least every active entry's modulus in that column. There is no tie rule beyond
  this inequality. Swap the current physical rows `k` and the chosen row, then
  subtract `S i k / S k k * S k j` from each strictly trailing entry. Store zeros
  outside that next active block, as in the accepted IE14 model.
- `entryMax A` is the finite maximum of the complex moduli of all entries.
  `activeMax S k` is the finite maximum restricted to `i.val,j.val ≥ k`.
  `growth A path` is the maximum over `k : Fin n` of
  `activeMax (trajectory A path k.val) k.val`, divided by `entryMax A`.
  The input is stage zero; stage `n-1` is the final scalar. Prove the finite
  maximum semantics and positivity of the denominator on valid inputs/paths.
- The growth set contains exactly the real values realized by some permitted
  dimension, banded nonsingular input and full admissible path. The conclusion
  is an actual `IsGreatest` statement and its `sSup` equality, not an equality
  to a placeholder supremum over conditional certificates.

## Integer recurrence and exact answer

Use natural-valued `h_p(0)=0` and, for `t : ℕ`,

\[
 h_p(t+1)=1+\sum_{r=0}^{p-1}h_p(t-r),
\]

where natural subtraction is harmless because all negative source indices
represent the same zero value `h_p(0)`. In particular the `r=0` term is `h_p(t)`.
Prove equivalence to the source's integer-index convention before using the
recurrence in correspondence claims. A strong-recursion definition must still
decrease its argument on every summand; it cannot assume an unproved recurrence.

Define the real target value to be `1` if `p=0`, and otherwise the real cast of
`h_p(p+q)`. Required generic recurrence facts include positive values for
positive arguments, monotonicity, and the exact canonical envelope state

\[
 x_i^{(t)}=1+\sum_{r=1}^{p-i+1}h_p(t-r)
 \quad(1\le i\le p,\ t\ge1),
\]

with first coordinate `h_p(t)`, last coordinate at least one, and the update
`(x1+x2, …, x1+xp, x1+1)`. Treat `p=1` without assuming a nonempty middle list.

## Universal upper bound obligations

1. Every nonsingular complex input has a complete admissible path. All path
   statements for the upper bound quantify over every such path.
2. For a banded input, prove the exact original-row provenance invariant at
   each stage. In one-based notation, original labels `i ≥ k+p` are untouched
   by the first `k-1` eliminations; only at most `p` older survivors plus the
   freshly eligible row can interact in the pivot front.
3. Prove the envelope inequality for an arbitrary pivot choice with multiplier
   moduli at most one. If using finite-subset sums instead of sorting, include
   every subset cardinality and its relation to the same envelope; do not only
   postulate a bound for the largest entry.
4. Fix an arbitrary target column `j`. For `j ≥ p+q+1` in one-based notation,
   all front target values vanish before stage `j-p-q`, and at most `p+q`
   updates affect a value before column `j` leaves the active matrices.
   For `j ≤ p+q`, start with the all-ones envelope after one imaginary update;
   at most `j-1` actual updates give `h_p(j) ≤ h_p(p+q)`. Keep bottom truncation,
   untouched rows, pivot-row entries and every active time in this argument.
5. Conclude, for arbitrary admissible `A,path,k,i,j`,
   `‖trajectory A path k i j‖ ≤ h_p(p+q) * entryMax A` on active indices for
   `p≥1`. Derive the stated growth bound by the actual maximum semantics.
6. For `p=0`, prove upper-triangular elimination has zero lower multipliers and
   exact growth one; no division by a possibly zero diagonal is allowed without
   the nonsingularity/path argument.

## Parametric attaining witness obligations

For `p≥1`, put `J=p+q+1`, `N=2p+q+1`, and `η=2^(-p)=(1/2)^p`.
The following construction uses one-based indices solely to match the source;
the future literal definitions must spell out its zero-based translation.

- `L0` is unit lower triangular with entry `-1` on the first `p`
  subdiagonals and zero elsewhere.
- The factor order is `σ=(p+1,1,2,…,p,p+2,…,N)`, and `P` satisfies
  `(P a)_i=a_(σ_i)`. This permutation is part of the explicit original matrix,
  not a preprocessing step of the algorithm.
- For `k<J`, the source vector `u^(k)` has first entry one when `k≤p+1`,
  entries `2^(i-2)` for `2≤i≤k≤p+1`, entry one at `i=k` when `k≥p+2`,
  and zero elsewhere. Set column `k` of `A` to `η Pᵀ L0 u^(k)`.
- Column `J` is one for `p+1≤i≤N` and zero otherwise. Each column `k>J`
  is the standard basis column `e_k`.

Prove all of the following for every `p≥1,q≥0`, without a finite parameter cap:

1. `N ≥ 1 + max p q`, all entries are rational real numbers embedded into `ℂ`,
   the exact band condition holds, and `entryMax A=1`.
2. For early columns, the required geometric-sum cancellations hold; their
   original-row support lies in `[k,k+p]`. The magnitude bound is at most
   `2^p` before scaling. Prove `η>0`, `η≤1`, and the exact scaled bound.
3. The first `J-1` actual GEPP steps can choose original labels in the stated
   factor order. In zero-based physical positions, the intended pivot is row
   `p` through the rotation prefix and subsequently the current diagonal row.
   Prove the physical swap/origin identity rather than assuming a pre-permuted
   input. Every selected pivot is nonzero and maximal in modulus; ties are legal.
4. The target column after factor-order elimination follows
   `u_i=c_i+Σ_(r=1)^p u_(i-r)`, with `c1=1`, `c2,…,c_(p+1)=0` and subsequent
   `c_i=1`. Prove `u1=1` and `u_i=h_p(i-1)` for `i≥2`. Thus an active entry
   at stage `J` has modulus `h_p(p+q)`.
5. The leading `J×J` block is nonsingular from these nonzero pivots and the
   remaining identity columns give a nonsingular whole matrix. This determinant
   conclusion must not be assumed as part of the witness definition.
6. Extend the admissible prefix to a full path with the same preceding states,
   if using that optimization. Combine the visible attaining entry with the
   independently proved universal upper bound to obtain exact growth equality.

For `p=0`, use the identity at dimension `q+1` and its actual GEPP trajectory.

## Full final contract

For every `p,q : ℕ` with `p ≠ q`, prove that the above target value is the
greatest element of the genuine growth set and equals its supremum. In
particular the set is nonempty and bounded above. Also export the universal
complex all-path upper bound and the nonsingular rational-real witness so the
source correspondence and the absence of hidden assumptions are auditable.

This is an exact-arithmetic classification. There are no precision variables,
probabilities, finite upper dimension, or rounded evaluations. Interval boxes
are unnecessary. If the optional exact LeanCert certificate for one half is
used, bind its output to the actual scale proof and use kernel trust throughout.

No theorem count, declaration spelling, or literal Lean signature is frozen by
this document. The future independent Challenge must expose the complete
contract and be reviewed independently before implementation.


## Planned literal declaration boundary

The definitions will use the same literal complex GEPP primitives as accepted
IE14 revision `6e48f25fffdae2cf93e4985dc515abbd15e0481b`, copied into the IE13
namespace with their exact bodies recorded in a reuse audit. No already-proved
problem-specific upper bound is imported. An explicit `gepp_model_semantics`
obligation exposes the physical swap and Schur recurrence again. The original
row map `origin` likewise retains the accepted literal swap composition.

The recurrence is implemented by a structurally recursive history register:
`recurrenceHistory p 0 r = 0`, and on each positive step its zero slot is one
plus the sum of the first p previous slots, while every positive slot shifts
from its predecessor. `bandSequence p t` is slot zero. Exported history and
recurrence equations must prove that this implementation is precisely the
integer recurrence above, with every beyond-the-start slot equal to zero.
This avoids any unproved well-founded recursion oracle.

The exact bound is `sharpBound p q`, the all-dimensional set is `growthValues p q`,
and its actual real supremum is `sharpConstant p q`. The final contract retains
`p ≠ q`; the upper bound and witness lemmas may prove stronger all-pair results.
The front's subset estimate is an exported conclusion over arbitrary subsets of
actual surviving original labels, not an assumption in the input predicate.

The witness is first defined as `witnessRational p q`, a matrix over ℚ, and then
entrywise embedded into ℂ as `witnessMatrix p q`. All arithmetic, powers, finite
sums and the inverse factor-row labeling are literal. `witnessSeedPath p q`
performs actual row swaps; its prefix through the first `p+q` eliminations is
proved admissible. The target entry at zero-based stage `p+q` is the current
diagonal entry with that same index. A separately proved prefix-extension
contract constructs a full admissible path preserving all states up to there.
No determinant, pivot validity, front bound or growth conclusion occurs as an
assumption in the witness definition.

The only routine proof terms allowed while forming these definitions establish
`Fin` index bounds from the literal dimension `2*p+q+1`; they prove no solution
obligation. The independent Challenge may contain deliberate `sorry` bodies;
there is no Solution or proof module at this phase. Every eventual advertised
export must pass LeanCert's kernel trust assertion and a separate Comparator
check permitting only `propext`, `Classical.choice`, and `Quot.sound` or subsets.
