# NR-03 next diagnostic plan

**Author:** `/root/lean_iv01_next` (AI agent; this is an author optimization
note, not an independent referee report)

**Base:** candidate commit `d8b65ab13ee9c27e8909052de792f10322a51e1b`, whose
monolithic `Solution.lean` SHA-256 is recorded in `DRAFT-MANIFEST.json`.

## Failure being diagnosed

Run `34774320268` compiled `LeanCert.Tactic.Verification` and `Definitions`,
then exited `134` in `compile-Solution` after `63.126` seconds. The only raw
error is a Lean interpreter memory exception. The run never emitted public
declaration locations, so no individual theorem can be called the failing
obligation. The raw evidence is retained outside this scratch package at
`/tmp/nla-nr03-development-evidence/run-34774320268/extracted/`.

## Exact source changes

The existing core structural proof is retained. The 896 finite branches in
`maskBit_complement` are replaced by:

```lean
  revert i a
  decide +kernel
```

The existing statements of `singleton_identity`, `pair_identity`, and
`four_identity` are retained while their proof scripts become one closed
`decide +kernel` each. This removes repeated elaborator goal construction.
The prior `coreV_at_rep` structural proof and the prior `closed_arithmetic`
closed decision are unchanged.

The remaining proof declarations are copied exactly into modules, with imports
only adjusted to their new local module names. This is intended to separate
resource-heavy elaboration states, not to alter the certificate.

## Expected remote module order

`Definitions`, `Encoding`, `FamilyDefs`, `Index`, `Core`,
`FamilyIdentities`, `Certificate`, `Rank`, `Solution`. All direct Lean calls
remain sequential, one thread, `-M4096`, and timeout 120 seconds. The draft
driver records each stage and skips only descendants after a failure.

## Soundness and limits

`decide +kernel` uses kernel reduction once for a closed decidable proposition;
it does not use `native_decide` or add an axiom. This mode change is logically
conservative, but its resource behavior is empirical. In particular,
`pair_identity` still computes the same finite proposition through the existing
`DecidableRel maskSubset`. If it remains too large, split its row/bit
properties structurally in a subsequent source review.

No local compiler was run and no proof or CI result is claimed.
