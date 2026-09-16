# MI-04 actual statement-elaboration audit: run 35040116376

**Result: MI-04 statement elaboration failed. No statement freeze or proof
implementation is justified by this run.** The two failures are explicit
type-inference errors in Definitions; the independent Challenge cannot import
the missing object file and reaches none of its 21 obligations.

Reviewer: OpenAI Codex agent `/root/next_inequalities`. I authored the MI-04
statement package. This report is an actual runtime and source-identity audit,
not an independent mathematical referee approval. The two mathematical boundary
approvals are separately retained from `/root` and `/root/next_elimination`.
No local Lean, Lake, cache download, source repair, freeze, commit, push, or
workflow dispatch was performed for this audit.

## Actual execution and complete input binding

The read-only GitHub API fetch was performed after terminal status. The actual
run is `sgstepaniants/OpenProblemsInNLA/actions/runs/35040116376`, attempt 1,
checkout `32f2bd6520df49e45a782cd8813b377e8234d5cf`. Its single `statements` job
is `104617877093`, with conclusion `failure`. Execution is Ubuntu Linux x86-64,
UID 1001, with actual Lean version `4.33.1` (compiler commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`). The receipt records execution from
`2026-09-16T00:28:27.421150+00:00` to `2026-09-16T00:34:14.101478+00:00`.

Artifact `10424728704`, `lean-development-statements`, has ZIP SHA256
`da7ae17b630893d046643cfaed8c278a3dd941770218977cccf4cd43fe33f3ee`.
I checked this against the GitHub artifact digest and the actual job's upload
line; all eight ZIP members match the extracted files. The run, job, artifact,
raw log, ZIP, and extracted receipt/log bytes are retained under `runtime/`.

The independent `audit.py` in this report directory checked all of the following:

- The receipt's source-key set is exactly the 216 tracked `.lean-development`
  inputs at the actual Git commit. Every input hash matches its Git blob, and
  exact copies are retained under `git-inputs/`.
- All seven commands have the expected argument vectors, recorded exit codes,
  complete log hashes, and unchanged pre/post source maps. Each complete command
  log occurs contiguously in the actual timestamp-stripped GitHub job log.
- All ten actual dependency revisions match both the committed development
  manifest and the held MI-04 manifest. In particular Mathlib is
  `0df444a360eaa60ab8c11dca51a86af692955474` and LeanCert is
  `621a43d7cf21f87872392a01e874f2f1dbddc926`.
- All 27 held MI-04 package inputs remain unchanged. The actual Definitions,
  Challenge and numerical statement bytes are exactly those approved by the two
  mathematical reviewers.

I also ran the existing `audit_development_run.py`, which performs source/log
auditing only. Its generated file is named `ROOT-AUDIT.json` and its generic
`reviewer` field says `/root`; I executed that script, so that field must not be
read as a separate root review of this run. My independently implemented audit
and author-role disclosure are in `AUDIT.json`.

## Every command result

| Command | Exit | Actual result |
| --- | ---: | --- |
| `lean --version` | 0 | Lean 4.33.1, Linux x86-64 |
| `lake env true` | 0 | All ten pinned dependencies checked out |
| `lake exe cache get` | 0 | Remote Mathlib cache fetched on the Linux runner |
| `lake build NLA.MI04.Definitions` | 1 | Two unannotated star-algebra equivalence applications fail |
| `lake env lean Challenges/MI04.lean` | 1 | Missing `NLA.MI04.Definitions.olean`; zero obligations reached |
| `lake build NLA.MF22.Norms NLA.MF22.ScalarCertificates` | 1 | Norms built; ScalarCertificates failed |
| `lake env lean Challenges/MF22.lean` | 0 | All 22 intentional specification placeholders elaborated |

## Concrete MI-04 diagnostics and narrow proposed remedy

The Definitions hash is
`cfd0c1e0174699e8e9127a6fb8b7ce9de3f4c7d9770292746d15c0a5bc047748`.
The actual module log reports `Function expected at Matrix.toEuclideanCLM` at:

- `NLA/MI04/Definitions.lean:32:14`, the call in `realQuadratic`;
- `NLA/MI04/Definitions.lean:85:46`, the call in `matrixCoefficient`.

In each case Lean leaves the scalar/index metavariables of the bundled
star-algebra equivalence unresolved. The already explicitly instantiated call
in `spectralNorm` has no reported error. The corresponding narrow proposed
repair is to instantiate `(n := ι) (𝕜 := ℂ)` in `realQuadratic`, and
`(n := Fin n) (𝕜 := ℂ)` in `matrixCoefficient`. This report applies no edit and
does not claim that the proposed repair has passed elaboration.

The Challenge hash is
`ca80d090bfe9f3013d08aa86297761e1e524810881bce92776896545d6eeabf9`;
the numerical obligations hash is
`5cb5e20ffcf035b2ea303cf9edae2e85619b0f562bf302cf6df0c7a46079d1d7`.
The retained Challenge source still contains the exact 21 approved genuine
obligations, with their full universal positive-block premise and affine
Hermitian conclusion. However, its actual output consists solely of the missing
Definitions object-file diagnostic at line 8. There are **zero** declaration
placeholder warnings in this run. The 21 source declarations must not be
reported as 21 successfully checked statements, still less as 21 proofs.

## Unrelated MF-22 outcomes preserved

The MF-22 Definitions and Norms modules built. The actual axiom output for
`NLA.MF22.complex_entry_norm_bound` is exactly the ordinary three axioms
`propext`, `Classical.choice`, and `Quot.sound`. This is component evidence only.

`ScalarCertificates.lean` failed at lines 29, 50, 54, 63, and 116. The raw goals
retain the imaginary part of a real-cast square, unreduced scalar conjugates,
and the polynomial-constant identity `C 5 * (C 10 - C 6) = C 20`. Subsequent
LeanCert checks correctly reject the resulting declarations that depend on
`sorryAx`; these failures are not suppressed. The complete 371-line module log
is retained. The MF-22 author and root received the exact diagnostics.

The independent MF-22 Challenge command succeeds with 22 intentional `sorry`
warnings. That is statement elaboration only, and does not rescue the failed
proof module or establish a full MF-22 theorem.

## Remaining gates and sealed records

The receipt explicitly says `mathematical_verification: false` and
`comparator_run: false`. No canonical default-kernel replay, Comparator match,
sandbox/control suite or whole-problem verification occurred here. A reviewed
syntactic repair and another actual successful MI-04 declaration run are needed
before a freeze; complete proofs and canonical checking remain later work.

`AUDIT.json` SHA256:
`3be5addef53d63ad4eceee3c9b341e9b31c9a721f6f85979bdcdbd10d4766d2d`.
`INPUTS.json` SHA256:
`d4e82935e1711788df60ebb7f284539941420408aafc2052ab77f3efb8a9b9d4`.
The input manifest binds the exact retained Git sources, runtime evidence,
auditing tools and audit result. No problem count, canonical status, permanent
ID, mathematical credit or publication was changed.
