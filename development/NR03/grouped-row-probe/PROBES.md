# NR-03 grouped closed-row benchmark: interfaces before implementation

Base commit: `5125bea6feff36fc1a602be1b14dfc62edd55733`.

This is a private development experiment, not a canonical statement amendment or a full-family verification claim. The target block predicates are exactly those already fixed for the previous pair/four eight-row probes: every row 120–127 against every column `b : Mask7`. Only the intended proof organization changes. The original full-family statements, full ten-export boundary, all earlier Lean source, and the previous successful/failed probes remain unchanged historical inputs.

## Intermediate row interfaces

`Mask7` is the existing `Fin 128`. Each intermediate interface below quantifies all 128 columns at one literal row. The fresh `NLA.NR03.GroupedProbe` namespaces prevent collisions with retained earlier probes.

```lean
namespace NLA.NR03.GroupedProbe.Pair

theorem row120 : ∀ b : Mask7,
    pairSum (120 : Mask7) b = pairClosed (120 : Mask7) b

theorem row121 : ∀ b : Mask7,
    pairSum (121 : Mask7) b = pairClosed (121 : Mask7) b

theorem row122 : ∀ b : Mask7,
    pairSum (122 : Mask7) b = pairClosed (122 : Mask7) b

theorem row123 : ∀ b : Mask7,
    pairSum (123 : Mask7) b = pairClosed (123 : Mask7) b

theorem row124 : ∀ b : Mask7,
    pairSum (124 : Mask7) b = pairClosed (124 : Mask7) b

theorem row125 : ∀ b : Mask7,
    pairSum (125 : Mask7) b = pairClosed (125 : Mask7) b

theorem row126 : ∀ b : Mask7,
    pairSum (126 : Mask7) b = pairClosed (126 : Mask7) b

theorem row127 : ∀ b : Mask7,
    pairSum (127 : Mask7) b = pairClosed (127 : Mask7) b

theorem high_rows : ∀ (r : Fin 8) (b : Mask7),
    pairSum (Fin.natAdd 120 r) b =
      pairClosed (Fin.natAdd 120 r) b

end NLA.NR03.GroupedProbe.Pair

namespace NLA.NR03.GroupedProbe.Four

theorem row120 : ∀ b : Mask7,
    fourSum (120 : Mask7) b = fourClosed (120 : Mask7) b

theorem row121 : ∀ b : Mask7,
    fourSum (121 : Mask7) b = fourClosed (121 : Mask7) b

theorem row122 : ∀ b : Mask7,
    fourSum (122 : Mask7) b = fourClosed (122 : Mask7) b

theorem row123 : ∀ b : Mask7,
    fourSum (123 : Mask7) b = fourClosed (123 : Mask7) b

theorem row124 : ∀ b : Mask7,
    fourSum (124 : Mask7) b = fourClosed (124 : Mask7) b

theorem row125 : ∀ b : Mask7,
    fourSum (125 : Mask7) b = fourClosed (125 : Mask7) b

theorem row126 : ∀ b : Mask7,
    fourSum (126 : Mask7) b = fourClosed (126 : Mask7) b

theorem row127 : ∀ b : Mask7,
    fourSum (127 : Mask7) b = fourClosed (127 : Mask7) b

theorem high_rows : ∀ (r : Fin 8) (b : Mask7),
    fourSum (Fin.natAdd 120 r) b =
      fourClosed (Fin.natAdd 120 r) b

end NLA.NR03.GroupedProbe.Four

```

Each block theorem covers exactly 8 × 128 = 1024 ordered pairs, one sixteenth of the existing full 128 × 128 family obligation. `Fin.natAdd 120 r` has value `120 + r.val`. Every intermediate numeral is below 128, so its `Mask7` representation has the stated value without wraparound. No arithmetic definition, hypothesis, or column restriction is introduced.

## Assembly plan fixed before proof implementation

Use one module for Pair and a second independent module for Four, both importing existing FamilyDefs. Within each module, give each of its eight row interfaces an individually closed `decide +kernel` proof. Then introduce only `r` in `high_rows`, enumerate `r : Fin 8` with `fin_cases r`, and discharge each resulting universally quantified column goal with the corresponding row lemma. The finite injection and literal row values agree definitionally; the assembled block introduces no new finite arithmetic decision. The block's exact predicate matches its previously frozen eight-row counterpart.

Print axiom diagnostics for each row lemma and the assembled block. The row diagnostics make partial progress visible if a later declaration fails. Any post-error diagnostic containing an elaboration placeholder is failed evidence, never an accepted proof. The two block diagnostics must be assessed together with their module exit codes. No native decision or extra axiom is permitted.

## Bounded diagnostic scope

The draft driver compiles Definitions, Encoding and FamilyDefs, then the two grouped modules independently. A failed Pair module does not block Four. All previous full proof modules and earlier probe modules remain byte-identical inputs but are not compiled in this benchmark. The existing workflow, Lake configuration, manifest, toolchain, pins, command execution, source retention and branch guard remain unchanged.

Every direct Lean module, including an entire eight-lemma grouped module, must fit the existing 4096 MiB limit, one thread, and 120-second external timeout. The job remains capped at 30 minutes. No local Lean/Lake invocation or cache download is allowed. No resource increase, live edit, push or new job is part of this private preparation. Root must review the exact five-file overlay before one existing-branch push.

The prior successful one-row probes establish only rows 120 and 127 for each family. This new experiment must report its actual outcome, source/Git hashes, pins, raw axiom diagnostics, and module times. Even if both blocks succeed, all other rows and the original complete NR-03 proof remain outstanding. No canonical status, PR, or campaign increment follows from this experiment.
