# Proposed MI-04 explicit type-argument repair

This proposal changes exactly two bundled map applications in a separate copy
of Definitions. The author package is unchanged. Both independent reviewers
must approve the proposal, and an actual Linux declaration run must pass,
before the statement package can be frozen or proof implementation started.

Actual run `35040116376` at Git
`32f2bd6520df49e45a782cd8813b377e8234d5cf` reports `Function expected at
Matrix.toEuclideanCLM` at Definitions lines 32 and 85. Its displayed type has
unresolved scalar and coordinate metavariables. The independent Challenge then
cannot import Definitions.olean and reaches zero of its 21 statements.
The complete authentic logs are retained in `actual-run35040116376/`; the sealed
runtime audit is in the sibling `MI04-statement-elaboration-35040116376` report.

The proposed file is `proposed/NLA/MI04/Definitions.lean`. It instantiates:

- `(n := ι) (𝕜 := ℂ)` for the operator in `realQuadratic`;
- `(n := Fin n) (𝕜 := ℂ)` for the operator in `matrixCoefficient`.

These are exactly the scalar and coordinate types of the existing arguments.
The already explicit call in `spectralNorm` uses the same pattern and produced
no error. The chosen operator remains the genuine complex Euclidean operator
from the same pinned Mathlib star-algebra equivalence. Neither definition's
parameters or mathematical body changes apart from spelling these implicit
types explicitly. No import, norm, order, hypothesis, quantifier, conclusion,
Challenge signature or numerical statement is changed.

`original/` retains the pre-edit definition bytes, all 21 Challenge declarations,
numerical obligations and their earlier draft manifest. `Definitions.patch`
contains the entire two-line diff. `CHANGES.json` binds both versions and the
unchanged statement hashes. No proof implementation, local Lean/Lake command,
workflow dispatch, commit, push, canonical edit or freeze was performed.
