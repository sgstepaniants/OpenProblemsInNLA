# RA-02 Matrix-scope amendment review

**Approve this exact syntax-only amendment for the next Linux statement
elaboration attempt.** It resolves the source-level integration finding without
changing the mathematical statements. It does not establish successful
elaboration, a statement freeze, proof implementation or problem verification.

The amendment is root-authored and sealed by manifest
`4ba11c4fab5fc0b4ba40192c3993511aecf74129f0211c4588580b498c23fb3e`.
The proposed Definitions hash is
`1a0f251cfcc38f57787de3ee79dc8c89e7bf0f496ebfe9196a66f8b3f452a376`;
the proposed Challenge hash is
`eb95beaddd92fc1b24d2df1d7bc9db9afec7a3391759dd2d613119c5f25d4340`.

Reviewer: `/root/ie13_continuation`. I reported the omitted scope and
recommended this narrow correction; `/root` authored the amendment. This
review verifies that mechanical correction and its byte boundaries. It is not
an independent rediscovery or a new complete mathematical review. The two
original nonauthor full-statement approvals remain separately attributed to
root and `/root/mi04_independent_referee`.

I read the full original Definitions and all 27 Challenge statements during
the immediately preceding integration review. Whole-file comparison now proves
that each proposed file differs solely by adding `Matrix` to its existing
`open scoped BigOperators ComplexOrder` line. Every other byte is unchanged,
including every definition, all 27 complete theorem headers and their deliberate
placeholders, imports, numerical constants, hypotheses, target quantifiers and
credit. The original 62-file draft and both full-statement review seals rehash
unchanged. All seven amendment inventory entries also rehash correctly.

The retained primary `Mathlib/Data/Matrix/Mul.lean` matches its literal Git
object at pinned revision `0df444a360eaa60ab8c11dca51a86af692955474` and has
SHA-256 `9ce6ecd0751e977f58fc47d6f271dff381e59868474a6955730ff07a99aa0e6b`.
I read its namespace context and the definition/notation at lines 692–708.
`*ᵥ` is scoped in namespace Matrix and expands to the genuine `Matrix.mulVec`,
whose entry is the finite row-vector dot product. Opening that scope in both
files selects the already intended quadratic form and eigenvector equation.
No proxy product or theorem-valued premise is introduced.

The omission was diagnosed from pinned source and SF-01's analogous actual
compiler failure. **No RA-02 compiler failure or successful run has yet been
observed.** The source files still contain no implementation or freeze. The
original immutable v1 integration report remains changes-requested; a v2 batch
must explicitly bind these two replacement hashes and receive its own final
integration review.

The bounded Python/Git audit passed. Its initial private inventory reader
needed the original draft's `all_files` field supported; that audit-only
adjustment changed no reviewed source or packet. No Lean/Lake/cache execution,
network call, worktree/Git mutation, publication or count increase occurred.
George Stepaniants's Caltech department/university formalization credit and
Colbrook's mathematical credit are unchanged; no email is introduced.
