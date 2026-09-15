# IE-17 Lean formalization

This package formalizes Matthew J. Colbrook's negative resolution of both
backward-error monotonicity questions in the canonical IE-17 problem. George
Stepaniants, Department of Computing and Mathematical Sciences, California
Institute of Technology, Pasadena, California, USA, is the formalization author.

The complete implementation and all seventeen exported LeanCert kernel
assertions passed [GitHub-hosted Linux run 35017536835](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35017536835),
at development commit `8070ed199166429ffd5ea3091caa940de6af5568`, as user 1001.
Every exported declaration's measured transitive axioms were exactly
`propext`, `Classical.choice`, and `Quot.sound`. The accepted source hashes and
actual log are retained in [the development receipt](verification/development-35017536835/SOURCE-RECONCILIATION.json).
**Standalone canonical Comparator/default-kernel replay and final independent
compiled-source reviews remain pending; this package is not yet counted as
complete.**

The exact statement boundary received two independent AI-agent approvals before
proof implementation. Two separate referees subsequently reviewed the complete
proof source. Historical draft comments in the frozen statement files are
preserved by `STATEMENT-FREEZE.json` and do not supersede the later dated records.

`NLA/IE17/Definitions.lean` contains the original mathematical objects.
`Challenge.lean` declares all seventeen targets in a separate environment with
deliberate placeholders. `Solution.lean` imports the completed proof route and
never imports Challenge. Its LeanCert assertions request kernel-level trust for
all seventeen declarations and succeeded in the recorded development run.

The principal result gives successive, nonzero exact LSMR iterates with

`μ(x₁)² ≤ 1979/2000 < 99/100 < μ(x₂)²`,

and also `μ̃(x₁)² < 503/500 < 1007/1000 < μ̃(x₂)²`. The exported theorems
`NLA.IE17.not_spectralMonotonicity` and
`NLA.IE17.not_projectionMonotonicity` negate both complete original universal
claims. [SourceCorrespondence.md](SourceCorrespondence.md) maps all seventeen
obligations to the canonical problem and Colbrook's exact source.

The proof preserves the induced Euclidean operator norm, exact LSMR minimization
over every vector in the actual Krylov span and the minimum-length convention.
It proves that the norm minimum over all feasible real perturbations is attained,
and verifies all four Penrose identities for the augmented inverse before
reducing its projected norm to rational scalar expressions.

Exact rational LDL factorizations certify the two small positive-definite
matrices. The universal lower bound uses the unnormalized new residual, which
eliminates square-root interval computations; the zero-new-residual case is
covered separately. The upper certificate includes a genuine operator-norm
bridge. Supplementary Python arithmetic only supplies rational data that Lean
must prove correct.

The original proof is credited to Matthew J. Colbrook, Department of Applied
Mathematics and Theoretical Physics, University of Cambridge. Formalization and
independent AI-agent reviews are distinct from external human peer review,
source-author endorsement and mechanical kernel verification. Source, scope,
automation and current verification status are recorded in `formalization.yaml`.

## Reproduce

With Lean installed, run from this project directory:

```bash
lake exe cache get && lake build +Solution
```

The [shared Linux verification guide](../../../docs/lean/README.md) describes
the additional Comparator, default-kernel replay and rejection checks. This
standalone package selects Solution by default and corrects the inherited root
manifest package name to NLAIE17; all exact dependency objects and all reviewed
mathematical sources are unchanged. The original statement-phase configuration
is retained under reviews/statement-phase/frozen.
