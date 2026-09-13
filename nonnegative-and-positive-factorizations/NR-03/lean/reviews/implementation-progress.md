# NR-03 implementation checkpoint

Reviewer/implementer: `/root/lean_iv01_next` (AI agent), 13 September 2026.

The implementation in `Solution.lean` now uses Holden's four source families
(complementary pairs, singleton corrections, pairs, and four-sets) and a
127-atom `Fin` index.  The expensive `decide` over all 16,384 entries and 64
core terms was removed.  The core family is reduced structurally to the unique
canonical representative (`coreW_indicator` plus `Finset` sum reduction), with
the remaining complement-dot equality isolated as a row-local finite check.
The remaining finite
family checks have only 7, 21, and 35 summands; the closed-family identity is
reduced to the two cardinalities `s = |b|` and `t = |a ∩ b|` with
`0 ≤ t ≤ s ≤ 7`.  The Boolean-vector to mask bridge is an explicit theorem
before the matrix certificate is consumed.

No local Lean compilation is claimed at this checkpoint.  After the prior
11-GB experimental reduction was terminated, all future local runs must use
`/tmp/nla-lean-formalization/bounded_lean.py` (Lean `-M 2048`, one thread,
90-second wall limit); heavy proof checks belong on Linux CI.  The prior
interrupted log/source remain outside this package.  No Git or PR changes were
made.

Current bounded-risk notes for final reviewers:

* `sourceW_core`/`sourceV_core` and the three other branch maps now use direct
  index arithmetic (`simp` plus bounded `omega`), so the family decomposition
  does not enumerate mask rows while proving index maps.
* `coreW_indicator` now uses the two cases `a.val < 64` and its complement,
  with `Fin.ext` and arithmetic, rather than a 128-by-64 enumeration.  The
  remaining singleton, pair, and four-set identities are row-split kernel
  checks; the four-set check is the largest remaining arithmetic reduction.
  The closed-family identity is reduced separately to a 64-case `Fin 8`
  cardinality calculation, with structural bounds `maskDot ≤ maskCard ≤ 7`.
* `generic_scaled_identity` casts the proved natural full-family identity and
  uses the explicit `natTarget_cast` theorem.  The general denominator bridge
  distributes a common positive denominator through the actual finite matrix
  product and proves factor nonnegativity.
* The Boolean-vector bridge now uses `encodeNat`, an inductive binary encoder
  with an inductive `< 2^n` bound, and `Nat.testBit_two_pow_mul_add`.  This
  replaces the earlier 896-case enumeration of Boolean functions and keeps
  the mask representation definitionally tied to all seven coordinates.
* `lakefile.toml` registers `Solution` and makes it the default target.  The
  candidate appends one `#assert_trust kernel` and one `#print axioms` command
  for each of the ten public exports; these are harness inputs, not evidence
  of a successful compilation until the remote run completes.
* The only unverified state is elaboration under the resource cap and later
  independent final review; no current claim of Lean verification is made.
