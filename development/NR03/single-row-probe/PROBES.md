# NR-03 single-row family probes: statements before implementation

Base commit: `855863c1babc9b9385239dc5a642efa236d4999a`.

These are four independent development benchmarks. They do not replace or weaken the full `pair_identity` or `four_identity` statements, or any of the original ten exports. The earlier eight-row probes are preserved as historical source inputs but are not compiled by this diagnostic. Their actual pair/four results were kernel-memory failures under the unchanged limit; the singleton eight-row probe passed. No result here is a full-family or full-problem verification claim.

## Exact fixed domains

`Mask7` is the existing abbreviation for `Fin 128`. The fixed rows `(120 : Mask7)` and `(127 : Mask7)` have values 120 and 127, respectively. Their seven-bit encodings have four and seven ones. Each column variable `b : Mask7` still ranges over all 128 columns. Each helper therefore checks exactly 128 pairs, one 128th of its full 128 × 128 family obligation. These two fixed rows neither cover all rows nor establish a uniform cost bound for other rows.

## Exact restricted helper statements

```lean
namespace NLA.NR03.Probe

theorem pair_row120 : ∀ b : Mask7,
    pairSum (120 : Mask7) b = pairClosed (120 : Mask7) b

theorem pair_row127 : ∀ b : Mask7,
    pairSum (127 : Mask7) b = pairClosed (127 : Mask7) b

theorem four_row120 : ∀ b : Mask7,
    fourSum (120 : Mask7) b = fourClosed (120 : Mask7) b

theorem four_row127 : ∀ b : Mask7,
    fourSum (127 : Mask7) b = fourClosed (127 : Mask7) b

end NLA.NR03.Probe
```

The statements call the existing exact definitions from FamilyDefs. They add no hypothesis, auxiliary arithmetic implementation, or restricted column domain. The numerals denote the required values without wraparound because both are strictly below 128.

## Intended proof and diagnostic behavior

Only after fixing these statements, each helper will receive one closed `decide +kernel` proof in a separate new module importing FamilyDefs. Raw `#print axioms` output will supplement each compile result. A diagnostic printed after an elaboration error is not accepted proof evidence. No native decision or extra axiom is permitted.

The driver draft will compile Definitions, Encoding, and FamilyDefs, then all four probes separately. A failure of one probe must not skip any other probe. All previous Lean files, including the original full proof modules and the earlier eight-row probes, remain byte-identical. The existing workflow, Lake configuration, manifest, toolchain, and resource settings remain byte-identical.

Every direct Lean module retains one thread, its 4096 MiB limit, and its 120-second external timeout. The existing workflow retains 30 minutes. No local Lean/Lake process or dependency download is allowed. This private draft starts no run. Root must review the seven proposed changed/added files before a single existing-branch push. Any later actual result must retain raw Linux logs, source hashes matched to Git, dependency pins, and measured per-probe times. Success would still leave all other rows and the original complete NR-03 boundary unestablished; no canonical status, PR, or campaign count change follows from these probes.
