# NR-03 complete row-certificate interfaces, frozen before bodies

Base commit: `91a1588f3141580cd1a0b95b6d22a7b32681fa97`.

This private fallback targets exactly the three existing family identities, with their complete original quantifiers. It is not a claim of successful compilation, canonical verification, or a status/count change.

```lean
theorem singleton_identity : ∀ a b : Mask7,
    singletonSum a b = singletonClosed a b

theorem pair_identity : ∀ a b : Mask7,
    pairSum a b = pairClosed a b

theorem four_identity : ∀ a b : Mask7,
    fourSum a b = fourClosed a b
```

`Mask7` is the existing `Fin 128`. The exact intermediate interfaces are enumerated in `COVERAGE.json`: for each family and literal row N from 0 through 127, one theorem universally quantifies every column `b : Mask7` and states the corresponding existing `familySum (N : Mask7) b = familyClosed (N : Mask7) b`. There are no new hypotheses, altered arithmetic definitions, omitted rows, restricted columns, or renamings of the original three family theorems or ten public exports. Since each literal N is below 128, its Fin numeral has value N without wraparound.

Every family uses the same complete partition:

| Block | Literal rows |
| --- | --- |
| 00 | 0–7 |
| 01 | 8–15 |
| 02 | 16–23 |
| 03 | 24–31 |
| 04 | 32–39 |
| 05 | 40–47 |
| 06 | 48–55 |
| 07 | 56–63 |
| 08 | 64–71 |
| 09 | 72–79 |
| 10 | 80–87 |
| 11 | 88–95 |
| 12 | 96–103 |
| 13 | 104–111 |
| 14 | 112–119 |
| 15 | 120–127 |

Each block file will contain eight separately closed `decide +kernel` row lemmas, followed immediately by their raw axiom diagnostics. There are 48 files, 384 literal-row lemmas, and exactly 128 × 128 ordered pairs per family. Fresh namespaces `NLA.NR03.RowCertificate.Singleton`, `.Pair`, and `.Four` avoid collisions with retained earlier probes.

Each full original family theorem will introduce only `a`, enumerate its 128 finite cases, and apply the matching row theorem while leaving `b` universally quantified. This avoids varying `Fin.natAdd` codomains entirely: the interfaces and assemblers use literal rows. Each full family theorem will have an axiom diagnostic. A diagnostic following an elaboration error is not an accepted proof.

## Sequential build plan

The heavy modules form one explicit import chain: Singleton blocks 00–15, then Pair 00–15, then Four 00–15. The first imports existing FamilyDefs; every later block imports its predecessor. These imports enforce sequential compilation of the heavy kernel reductions in ordinary Lake builds, without modifying shared workflow infrastructure or relying on an unverified global concurrency setting. FamilyIdentities imports the last block and existing Core. No final target imports historical probe modules.

The development driver will restore Definitions, Encoding, FamilyDefs, Index, Core, the 48 ordered row modules, FamilyIdentities, Certificate, Rank, and Solution. The existing LeanCert Verification support module remains. Every direct module, including full FamilyIdentities, keeps the same 4096 MiB, one-thread and 120-second limits; the existing job remains 30 minutes. No budget increase is authorized if the graph runs too slowly.

The only planned existing proof-body changes are the three family assemblies and the already reviewed `Nat.pow_pos hp _` → `Nat.pow_pos hp` API correction in `Certificate.genericD_positive`. All original definitions, other helper bodies, and the entire ten-export statement boundary stay unchanged. Earlier probes and evidence remain preserved as uncompiled source inputs in this development package. This private fallback can later be combined with a separately reviewed structural Singleton/Pair proof before any root-approved run.

No local Lean/Lake process, cache download, live source edit, Git mutation, workflow dispatch, or canonical status change is part of this generation task. The source generator and manifests will record the exact generated files and coverage. The actual full graph remains uncompiled until a separately approved remote run.
