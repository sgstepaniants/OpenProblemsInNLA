# IE-13: proof-body repairs for development run 35055219493

This append-only author packet binds the exact failed Linux commit
`dbc2371b74bcae58f6d6957bd588e32c56c8dc91` to 27 original active source files,
the frozen Challenge, the raw run/API/artifact/log evidence, and the repaired
27-file candidate. All 28 public theorem headers and all 10 frozen files remain
unchanged. Every helper declaration header and import also remains unchanged.

The actual run compiled the frozen statements but failed to compile the full
implementation. It did not run Comparator or the strict whole-proof checker.
The new candidate has **not been compiled**, either locally or remotely. No
problem status, accepted count, Git branch, commit, or publication was changed.

## Changes tied to the observed diagnostics

1. `WitnessColumns`, original line 107: use `simp only [hiff]` to transport the
   equivalent condition of an `ite`, so its dependent `Decidable` instance is
   handled by simplification rather than an ill-typed rewrite motive.
2. `Envelope`, original line 21: simplify the actual residual `if True` with
   `if_true`. The previous `if_pos rfl` was unused in the recorded diagnostic.
3. `Front`, original line 28: provide a local `classical` instance for the
   already-defined finite filter predicate. The finite injection argument and
   its claim are unchanged.
4. `TailAlgebra`, original lines 95, 102, 112: use `change` to expose the natural
   value of the local finite index before `omega`. The three obligations remain
   respectively `k ≤ i.val`, `k < T`, and `k < T`. The kernel must check these
   definitional conversions.
5. `WitnessOrder`, original line 64: in the branch `i = f`, where `f.val = p`
   and `k < p`, explicitly prove `¬ p < k + 1` and simplify the exact formula.
   This avoids treating constructor projections as unrelated arithmetic atoms.
   At original lines 101 and 114, make the now-redundant projection simplifier
   optional; the subsequent `omega` must still solve every remaining goal.
   At original line 135, simplify the recorded residual `if True` explicitly.

Only these five files have changed, and only inside existing proof bodies.
The implementation map is refreshed to point at the new hashes and line numbers.
George Stepaniants' Caltech Computing and Mathematical Sciences attribution,
Matthew J. Colbrook's original mathematical credit, and Apache-2.0 notices are
preserved. No email is added.

## Evidence and next gate

`BEFORE-BINDINGS.json` records every exact Git blob, receipt key, SHA-256, and
the normalized 28 public headers. In the development harness only the filename
changes from `Solution.lean` to `NLA/IE13/Complete.lean`; the bytes are identical.
The Challenge similarly appears under `Challenges/IE13.lean` with identical
bytes. `BEFORE-MANIFEST.json` seals the pre-edit packet independently.

`audit_repair.py` is a pure Python static audit of sealed snapshots, statements,
declarations, imports, source markers, and historical receipt log hashes.
Its output is not a Lean proof check. Full source review by other agents and a
new exact-commit Linux compilation are still required. Even a successful future
development build will not by itself constitute strict default-kernel and
Comparator acceptance.

The optional `try simp` calls only allow a no-op simplification to continue.
They cannot discharge a goal without a proof, and do not skip the mandatory
arithmetic proof. The primary pinned `Fin` order definitions are retained in
`primary/Mathlib/Data/Fin/Basic.lean` for the finite-index conversions.
