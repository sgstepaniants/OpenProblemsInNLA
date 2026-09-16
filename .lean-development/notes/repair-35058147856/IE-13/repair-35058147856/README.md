# IE-13: proof-body repairs for development run 35058147856

This separate author packet binds the actual failed Linux commit
`d36c8b357347a78781e854328a95fd5e4adce852` to all 27 active IE-13 sources,
the frozen Challenge, all 10 frozen files, and a complete repaired candidate.
Only seven existing proof bodies in three files change. All 238 declaration
headers, 28 public contracts, imports, mathematical definitions and frozen
bytes remain unchanged. The original mathematical target retains every
dimension and bandwidth, the full complex GEPP model, all permitted pivot
choices, the attaining rational construction, and the final greatest-value
and supremum claims.

The repaired candidate has **not been compiled**. No strict checker or
Comparator has run on it. The prior development run failed, and no new problem
acceptance, solved count or publication is claimed.

## Changes and the actual diagnostics

1. `WitnessEntries`, original line 44: permit the existing finite-constructor
   simplification to make no change. The recorded failure is exactly a
   no-progress `simp`; a separate mandatory `all_goals omega` still proves
   every remaining arithmetic branch. This does not admit or suppress an
   unresolved goal.
2. `WitnessForward`, original lines 80 and 113: replace the unused
   `if_pos rfl` argument with the pinned core `ite_true` theorem. The actual
   diagnostics display residual `if True` expressions in both places.
3. `WitnessForward`, original lines 129–131: prove the existing target-column
   identity by its three natural cases, `i.val < p`, `i.val = p`, and
   `p < i.val`. The first case has factor index `i.val + 1`, which is positive
   and at most `p`, so both sides equal zero. The second has factor index zero,
   so both sides equal one. In the third, the factor index is unchanged,
   positive and greater than `p`, so both sides equal one. The original broad
   conditional splitting left 11 contradictory branches; the replacement
   supplies the required natural inequalities before simplification. It adds
   no hypotheses and includes `p = 0`.
4. `LateColumn`, original lines 21, 28, 51 and 74: introduce local `classical`
   instances in the three affected proofs. The recorded failures request
   `DecidablePred` for the existing `oldRows`/`frontRows` filter predicates.
   The row sets, their statements, and all update arguments are unchanged.

## Exact binding and static checks

`BEFORE-BINDINGS.json` records the Git object and receipt hash for all 27 sources
and the Challenge. The development harness renames `Solution.lean` to
`NLA/IE13/Complete.lean` and the Challenge to `Challenges/IE13.lean`, without
changing their bytes. `BEFORE-MANIFEST.json` was written before any author
source edit. `before/`, `after/`, `frozen/`, and `actual-git/` retain the exact
versions. `repair.patch` is generated from all active snapshots.

`audit_repair.py` verifies all frozen bytes, all declaration headers, every
public contract, the seven permitted changed declaration bodies, imports,
source markers and receipt/log hashes. Its checks passed. This is a static
Python audit and does not establish Lean elaboration or kernel acceptance.
`IMPLEMENTATION-MAP.json` is refreshed only to the new source hashes and line
numbers; its complete-compilation and whole-problem flags remain false.

Pinned primary Lean and mathlib sources are retained under `primary/`, with
Git blob and SHA-256 bindings in `PRIMARY-API.json`. The specific APIs reviewed
are listed in `PRIMARY-API-NOTES.md`. This is a source review, not a local
execution of the Lean toolchain.

The complete authenticated earlier run and independent operational audit are
retained under `actual-run/`. That audit binds all 1,633 tracked development
inputs, all seven unchanged post-command maps, pinned dependency revisions,
and every nonempty log line to the authenticated raw GitHub job stream.
It found the previous five repaired IE-13 modules successfully built and the
three failures addressed here. The frozen Challenge elaborated with its 28
deliberate specification holes. The development workflow did not run strict
default-kernel replay, Comparator or their negative controls.

The reused `ROOT-AUDIT.json` has a legacy fixed `/root` label but was executed
by this child agent; the separate child review explicitly discloses this. Raw
API records are private evidence and must be excluded or appropriately
summarized before any future public submission to preserve contact privacy.

George Stepaniants' Caltech Department of Computing and Mathematical Sciences
attribution, Matthew J. Colbrook's original mathematical credit and Apache-2.0
notices are unchanged. No email was added to the sources. No development
worktree, Git branch, commit, workflow dispatch, PR or count was changed.

Two independent source reviews and a new exact-commit remote Linux run are the
next gates. Even a successful development build would still require the final
strict checker/Comparator campaign before whole-problem acceptance.
