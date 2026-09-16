# MI-04 independent incremental review: block extrema and invariance

Reviewer: OpenAI Codex AI agent `/root/next_elimination`, independent of the
MI-04 implementation author. This review applies the repository's scoped Tau Ceti
fidelity, correctness, proof-quality, reuse and attribution criteria. It is not
human peer review or official Tau Ceti certification.

**Verdict: APPROVE both new modules as mathematical source. No correction
requested.** Actual compilation is pending. This report does not approve the
complete MI-04 proof or claim LeanCert, default-kernel or Comparator acceptance.

The reviewed author handoff is `proof-handoffs/block-extrema/MANIFEST.json`,
SHA-256 `99b196f373f86bc43b7e2bfd6a239d5dd1ec9c0be8cd6f94fdb896ad3710ea62`.
The new complete sources are:

- `BlockSymmetry.lean`:
  `7d5c0e711ba01a8bb98616427b50b06c64768e3bb12aef81ab06cd03720d3826`.
- `ScaledSymmetry.lean`:
  `6ad9967e48602adc087ac905407f1554fc5e8fdb04f90dd9cea0605c8d350ef1`.

`INPUTS.json` binds retained exact snapshots, and `audit_inputs.py` reproduces
the source, header, immutable-Git and limited textual trust checks without
executing Lean. The accompanying `CHECKS.json` distinguishes those checks from
mathematical reading and from unperformed runtime verification.

## Scope and target fidelity

The two implemented main headers match the full frozen Challenge headers after
whitespace normalization: `universal_to_extreme_symmetry` and
`extreme_symmetry_scaled_unitary`. Definitions, all 21 Challenge contracts and
the numerical statement document remain at the reviewed frozen hashes.

The canonical target concerns every positive finite dimension and arbitrary
complex `X`, with the universal inequality over genuine Hermitian positive
semidefinite block completions in the Euclidean operator norm. The two new
modules prove the exact spectral-extremum reduction and the invariances needed
by the second-order argument. They do not replace the universal premise with a
preselected completion class, assume an eigenbasis, or impose invertibility,
normality, distinct values or positive definiteness. The full affine-Hermitian
conclusion and the intervening implications remain separate obligations.

I read both new modules in full, the complete `Unitary`, `Coordinates`, `Rayleigh`
and `Quadratic` dependency sources, the frozen definitions and contracts, and the
canonical and original Colbrook source. The previously reviewed second-order
limit remains a separate review; this report does not silently broaden that
report's claims.

## Boundary completion and the reverse inequality

Let `K=pencil X T` and `c=topValue (-K)`. The proof obtains `c≥0` from the two
actual unit coordinate vectors at matching positions in the two diagonal
blocks. Their real quadratic values are `-Re(T aa)` and `Re(T aa)`. Since both
are bounded by the genuine Rayleigh maximum, their inequalities force `c≥0`.
The positive dimension assumption supplies the coordinate. This avoids any
unproved trace-to-eigenvalue inference and works at `n=1`.

The already proved scalar-order equivalence gives `cI+K` positive semidefinite
at the exact spectral boundary, including when it is singular. Its literal
blocks are `A=cI+T`, `X`, `X*` and `B=cI-T`; both diagonal blocks are proved
Hermitian and `A+B=2cI`. Thus it is a valid actual instance of the original
universal hypothesis. The positive-matrix norm identity and scalar-shift rule
give `c+topValue K≤2c`, hence `topValue K≤c`. Nonnegativity of `c` justifies
the norm of the scalar matrix as `2c`, rather than an incorrectly unsigned
formula. No step divides by `c`, so the zero-boundary case is retained.

The matrix `J=diag(I,-I)` is constructed as an actual unitary group element.
Direct block multiplication gives `J*(-K)*J=K_X(-T)` with the correct signs in
both off-diagonal blocks. Invariance of the Rayleigh supremum under unitary
similarity identifies the extrema. Applying the same inequality to `-T`, which
is Hermitian, then gives the reverse inequality. The conclusion therefore holds
for every original Hermitian test matrix `T`; it is not just one direction of
the desired equality.

These steps implement the first subsection of Colbrook's manuscript. Its trace
argument is replaced by two explicit unit-vector inequalities. The replacement
proves exactly the nonnegativity needed and preserves all original cases.

## Unitary similarity and positive scaling

`Unitary.lean` maps each actual matrix unitary through the star-preserving
Euclidean continuous-linear-map equivalence to a genuine linear isometry
equivalence. The inner-product calculation has the correct adjoint orientation:
the quadratic form of `U* M U` at `v` is that of `M` at `Uv`. Norm preservation
and the inverse isometry give both inequalities between the actual Rayleigh
suprema. Hermitian invariance is a proved congruence, not a custom assumption.

For the block pencil, the new literal block unitary is `diag(U,U)`. To handle
an arbitrary Hermitian test matrix after conjugating `X`, the source sets
`T0=U T U*`, proves it Hermitian and verifies `U* T0 U=T`. Conjugating both
`K_X(T0)` and its negative thus yields the two required extrema for
`K_(U*XU)(T)`. The proof does not silently restrict `T` to diagonal or commuting
matrices.

Positive homogeneity of `topValue` is proved for every matrix and every real
`r≥0` from the actual maximum and its attaining unit vector. The scaling
invariance, whose frozen contract requires `r>0`, uses the literal Hermitian
test matrix `T0=r⁻¹ T`, proves `r T0=T`, and rewrites the full block pencil as
`K_(rX)(T)=r K_X(T0)`. The conjugate-transpose off-diagonal block scales correctly
because the scalar is real. Both extrema scale by the same nonnegative factor.
There is no unjustified use of homogeneity for a negative or complex factor.

The final wrapper composes these two complete invariances and matches the frozen
contract for every complex `X`, positive `r` and arbitrary unitary `U` in every
dimension `n≥1`.

## Foundations, efficiency, attribution and remaining gates

The consumed Rayleigh dependencies prove compact-unit-sphere attainment, the
positive-matrix operator-norm identity and scalar-order equivalence for the
actual `Matrix.toEuclideanCLM`. The chosen supremum is therefore neither empty
in positive dimension nor an unconnected surrogate for the needed spectral
quantity. Exact block identities use pinned Mathlib's block multiplication,
adjoint, real-scalar and unitary APIs. The relevant primary API files were
inspected and their retained contents compared to Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`.

The route is symbolic and independent of dimension in proof structure; no
interval subdivisions, numerical eigensolver or growing determinant expansion
is needed. Original mathematics remains credited to Matthew J. Colbrook,
University of Cambridge DAMTP. Formalization credit remains George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, with the existing AI-assistance disclosure and no personal
formalization-author email.

The reviewed six proof files contain no proof holes, new axioms, unsafe/native
shortcuts or Challenge imports. Each new frozen export has an axiom print and a
kernel-only LeanCert assertion. These are prospective gates until executed; I
did not run Lean/Lake locally, inspect a successful run of the new modules, or
edit the author's files. Actual Linux elaboration, measured transitive axioms,
Comparator/default-kernel and rejection controls, final-byte reconciliation and
two complete independent final reviews remain required before full MI-04
verification or publication.
