# NR-03 modular bounded diagnostic draft

**Status:** source-only optimization draft; not compiled, not verified, and not
countable.

This scratch package responds to the bounded failure at candidate commit
`d8b65ab13ee9c27e8909052de792f10322a51e1b` (GitHub run `34774320268`). The
failed run compiled LeanCert and `Definitions`, then the monolithic `Solution`
process terminated after 63.126 seconds with
`lean::memory_exception: excessive memory consumption detected at
'interpreter'`. No declaration location was emitted.

The approved `Definitions.lean` and placeholder `Challenge.lean` are copied
byte-for-byte from that candidate. The mathematical declarations are separated
into meaningful dependent modules so a bounded remote run resets elaborator
state after each stage:

1. `NLA.NR03.Encoding` — mask/vector encoding, bit correspondence, casts, and
   the all-Boolean-vector bridge.
2. `NLA.NR03.FamilyDefs` — exact atom families, source indexing and sums.
3. `NLA.NR03.Index` — the finite 127-index decomposition and source bridges.
4. `NLA.NR03.Core` — complementary core-pair reduction and core sum identity.
5. `NLA.NR03.FamilyIdentities` — singleton, pair, four-set and closed-family
   identities.
6. `NLA.NR03.Certificate` — full source identity, generic matrices, and the
   scaled certificate.
7. `NLA.NR03.Rank` — the real denominator bridge, factorization and rank
   consequences.
8. `Solution` — public trust/axiom diagnostics only.

The finite reductions are changed in two deliberately small ways. The 896-case
`maskBit_complement` proof now reverts both finite variables and invokes one
closed `decide +kernel`, removing the 128-by-7 interpreter-generated goal
forest. The three row-local family identities now invoke one closed
`decide +kernel` on their existing universal finite propositions, removing the
outer `intro a; fin_cases a` branching. `closed_arithmetic` already used a
closed `decide +kernel`. No target, definition, certificate family, Boolean
index, denominator, rank statement, or non-finite proof body is weakened.

The proposed mode remains a diagnostic: a closed kernel decision may still be
expensive, especially for `pair_identity` because `maskSubset` has a seven-bit
finite decision procedure. If `FamilyIdentities` still exceeds the bounded
remote limit, the next reduction should replace that individual closed finite
decision by structural coordinate/count lemmas. The module graph makes that
failure identifiable without re-elaborating the earlier modules.

The draft driver retains the existing remote bounds (`-M4096 -j1`, 120 seconds
per Lean module) and does not run a monolithic `lake build`. It is intended for
remote Linux only. No local Lean/Lake/cache process was run to create this
draft.

The public `Solution` file contains the same ten Comparator names and ten
LeanCert kernel assertions as the failed candidate, now supplied by imported
modules. The copied `Challenge.lean` remains outside the proof claim and still
contains its intentional placeholders. Comparator/default-kernel/sandbox
acceptance and publication metadata are pending.
