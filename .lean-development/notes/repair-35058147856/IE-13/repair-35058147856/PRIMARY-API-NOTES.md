# Pinned APIs inspected for this repair

All files are fetched from the exact Git revisions recorded in
`PRIMARY-API.json`, with their Git blob identities recomputed from the downloaded
bytes. The Lean revision is the one printed by the actual run's Lean 4.33.1
binary; the mathlib revision equals the authenticated dependency receipt.

The relevant inspected definitions and lemmas are:

- `src/Init/SimpLemmas.lean:237`: core `ite_true (a b : α)` proves
  `(if True then a else b) = a` by reflexivity. This is the replacement used in
  the two recorded residual conditional goals and the exact-zero factor case.
- `src/Init/Core.lean:1178–1203`: `if_pos`, `if_neg`, `dif_pos`, and `dif_neg`
  implement the nondependent/dependent conditional branches. The repaired
  target-factor proof supplies explicit natural inequalities for these rules.
- `src/Init/Classical.lean:81`: `Classical.propDecidable` is a noncomputable
  scoped instance for arbitrary propositions. It supplies the local instance
  required when applying finite-filter membership lemmas.
- `Mathlib/Data/Finset/Filter.lean:46,114,127`: `filter` and `mem_filter` require
  `DecidablePred`. The latter proves membership equivalent to original
  membership and the filter predicate. This matches all four observed
  `LateColumn` diagnostics.
- `src/Init/Prelude.lean:2324` defines `Fin` as a natural value and its strict
  bound. `src/Init/Data/Fin/Basic.lean:21` coerces it to that value. The existing
  `Fin.val_mk` simplification is kept optional where Lean has already reduced
  the constructor projection, and the arithmetic proof remains mandatory.

Only the relevant APIs and their surrounding source were inspected here;
retaining a complete primary source file does not assert a separate full-file
mathematical review of Lean or mathlib.
