# Independent authentication of development run 35058147856

Reviewer: `/root/ie13_continuation`. This is an operational audit of the actual
completed GitHub run, not a successful whole-problem proof certificate.

The authenticated run on `sgstepaniants/OpenProblemsInNLA` at
`d36c8b357347a78781e854328a95fd5e4adce852` concluded **failure**. Job
`104672556977` and artifact `10431791787` identify the same head. The artifact's
GitHub SHA-256 digest equals the downloaded archive digest. All 1,633 tracked
development inputs equal their exact Git blobs and the receipt. All seven
post-command source maps equal the initial map; dependency revisions match the
pinned manifest. Every nonempty line of every command log also appears in order
in the authenticated raw job log.

I read both complete implementation logs, both complete Challenge logs, the
version/dependency/cache logs, and the exact executed Python checker, project
configuration and workflow. The run used Lean 4.33.1 on Linux under UID 1001.
The pure Python/Git auditors used here did not invoke local Lean or Lake.

## Actual implementation outcomes

Both complete implementation commands exited 1. For MI-04, 14 modules were
reported built, including `Probes`. `BasisTransport` failed on two unresolved
orthonormality branches, the unavailable `Basis.toMatrix_apply` identifier and
an under-instantiated rewrite. Of 21 public contract names, 16 axiom reports
were printed: 15 list only the standard axioms; `orthonormal_pair_symmetry`
lists `sorryAx` from the failed elaboration. Five public reports were not
reached. This does not establish a verified MI-04 result.

For IE-13, 14 modules were reported built. All five modules repaired after the
previous run now build: `WitnessColumns`, `Envelope`, `Front`, `TailAlgebra`
and `WitnessOrder`. Failures advanced to `WitnessEntries` (a no-progress
simplification), `WitnessForward` (residual conditional cases) and `LateColumn`
(four missing decidability instances). Of 28 public contract names, 18 axiom
reports were printed: 17 list only the standard axioms;
`witness_structure` lists `sorryAx` from failed elaboration. The standard-axiom
report for `late_column_zero` occurs inside a failed module and is not a
successful module build. Ten public reports were not reached. This does not
establish a verified IE-13 result.

The exact module lists, all observed error lines and all public axiom reports
are retained in `OPERATIONAL-CHECKS.json`. The original logs remain authoritative
for complete diagnostic contexts. `ALL-1633-INPUT-BINDINGS.json` records the
complete Git/receipt comparison rather than only the repaired files.

## Statements and scope

The MI-04 and IE-13 Challenge commands exited 0 with exactly 21 and 28 deliberate
`sorry` warnings, respectively, and no errors. Those are specification files,
not submitted proofs. They establish statement elaboration only.

The development workflow did not run strict default-kernel proof replay,
Comparator, or their negative controls. These tools therefore cannot be claimed
to have passed on this commit. No source, Git state, count, publication, or new
workflow dispatch was changed by this audit.

The reused `audit_development_run.py` emits the fixed reviewer label `/root` in
`ROOT-AUDIT.json`. This child agent actually invoked it; that label does not
claim a separate root manual review. The separate child audit records its own
reviewer correctly. The evidence includes private raw API data; any later public
submission must apply the existing contact-email exclusion policy.
