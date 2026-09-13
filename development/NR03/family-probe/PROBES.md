# NR-03 restricted family probes: statements before implementation

Base commit: `70bf81ecc597d3f2266a19488fe2a4d6195a4632`.

These are three independent development benchmarks. They do not replace or weaken `singleton_identity`, `pair_identity`, or `four_identity`, which retain their full `∀ a b : Mask7` statements and original bodies. No probe is a full NR-03 verification claim. The latest full-family module timed out after 120 seconds without a declaration-level diagnostic; these probes measure each family separately.

## Fixed domain

`Mask7` is the existing abbreviation for `Fin 128`. For `r : Fin 8`, the expression `Fin.natAdd 120 r : Mask7` has value `120 + r.val`, hence runs through exactly rows 120 through 127. The column `b` still ranges over every `Mask7`. Each helper therefore covers exactly 8 × 128 = 1024 ordered pairs, one sixteenth of its existing full 128 × 128 obligation. These rows have four fixed high bits and up to three additional low bits; no claim is made that they bound the cost of other rows.

## Exact restricted helper statements

```lean
namespace NLA.NR03.Probe

theorem singleton_high_rows : ∀ (r : Fin 8) (b : Mask7),
    singletonSum (Fin.natAdd 120 r) b =
      singletonClosed (Fin.natAdd 120 r) b

theorem pair_high_rows : ∀ (r : Fin 8) (b : Mask7),
    pairSum (Fin.natAdd 120 r) b =
      pairClosed (Fin.natAdd 120 r) b

theorem four_high_rows : ∀ (r : Fin 8) (b : Mask7),
    fourSum (Fin.natAdd 120 r) b =
      fourClosed (Fin.natAdd 120 r) b

end NLA.NR03.Probe
```

The expressions call the existing exact family definitions without a reformulation, new arithmetic implementation, or sampled column domain. There are no new hypotheses. `Fin.natAdd 120 r` already carries its bound and has definitionally the required `Fin 128` type, so no extra arithmetic lemma is needed to express a probe.

## Intended proof and diagnostic behavior

Only after fixing the statements above, each helper will receive one closed `decide +kernel` proof in a separate module importing the existing FamilyDefs. All existing Lean source, Challenge, comparator mapping, toolchain, manifest, and Lake configuration bytes remain unchanged. The support driver draft will compile the already successful prerequisite modules, then all three probes independently; a failure in one probe must not skip either of the others.

Every probe retains exactly one Lean thread, the 4096 MiB Lean memory limit, and a 120-second external wall limit. The existing workflow remains byte-identical with its 30-minute job limit. No local Lean/Lake execution is permitted. Raw Linux logs and exact input hashes must be retained if the draft is later approved and pushed. Success at all three probes is still only a restricted benchmark: every omitted row and the full original ten-export proof boundary would remain to be established in a later complete proof. No canonical status, pull request, or campaign count changes are authorized by this draft.
