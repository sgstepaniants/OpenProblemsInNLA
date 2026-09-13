# NR-03 development-package setup notes

This is a source-only development package. Keep it separate from the canonical
NR-03 proof worktree until the current canonical remote run is terminal and
root has reviewed its result. Do not run `lake`, Lean, dependency setup, or
cache generation on macOS.

For a remote test, copy `development/NR03` into the same path in a clean
repository and copy `.github/workflows/lean-nr03-development.yml` into the
repository workflow directory. Use the dedicated branch
`codex/lean-nr03-nonnegative-rank`; the driver rejects other refs. The workflow
first records the exact tracked inputs, then the pinned Lean action prepares
the toolchain and dependencies, and finally invokes:

```text
python3 development/NR03/ci_compile.py --record-inputs
python3 development/NR03/ci_compile.py --compile
```

The driver expects the workflow environment variable `NR03_LOG_DIR`. Its
artifact contains `source-hashes.json`, exact input copies, ten dependency-pin
receipts, `module-dependencies.json`, per-command raw stdout/stderr,
`module-results.json`, `source-hashes-after.json`, and `result.json`. A failed
step remains evidence of development feedback only.

The compile order is LeanCert Verification, `NLA.NR03.Definitions`, and
`Solution`; Challenge is retained as the unchanged statement boundary but is
not compiled because its ten intentional placeholders are excluded from the
proof candidate. Each Lean process is one-threaded with `-M4096` and a 120
second wall-clock timeout. The workflow has a 30-minute job limit. No
aggregate `lake build`, Comparator invocation, axiom acceptance, or
publication-status update is performed.

The exact proposed Solution source is SHA-256
`4224164dd803b1d0418694acee1318517da39b47b16fd110955af42e7f779f28`; the
frozen Definitions source is SHA-256
`5157fd499d2f63d218012f96bee43f30e5f57e5a2353fde13878af46d30fda04`. The
workflow input manifest binds both and all configuration files. If a source
hash changes, the driver must fail before compiler feedback is interpreted.

Integration note: the coordinator reused the existing NR-03 branch after the
original run reached a terminal state. This avoids creating a second checkout
or triggering an unrelated all-project baseline run. The canonical proof and
status remain unchanged. Development compilation is not Comparator evidence.
The old canonical formalization.yaml is not copied into this reduced compiler
package; the canonical source retains its complete metadata and review files.
