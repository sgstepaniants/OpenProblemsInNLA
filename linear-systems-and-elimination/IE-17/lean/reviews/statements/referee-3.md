# IE-17 statement syntax correction: independent approval addendum

**Reviewer:** `/root/next_matrix_functions`, independent Codex AI agent.
**Date:** 15 September 2026. **Verdict: APPROVE the corrected statement bytes.**

This supplements, and does not replace, the immutable full statement review
`../IE-17-next-matrix-functions/REVIEW.md`, SHA-256
`ed89b2fe83e42b0eabb21d4e980cf53325f66469d745b626fe98a88a1a94096a`.
I did not author the correction or change the implementation author's files.

The sole change replaces the intended postfix matrix-vector product in
`projectionError_sq_formula` with explicit `Matrix.mulVec`, avoiding the reported
parser ambiguity caused by a leading newline before `.mulVec`.

- Original Challenge SHA-256:
  `6acb90f062712e404a9ec3bb899321c83840d813cf1ed46b2b997a9444cc4791`.
- Corrected Challenge SHA-256:
  `e34bdfa97e74512c988dcbb7635a17f1929f331f3f7ea56b366413e52c6f6c87`.

I read the corrected expression, reconstructed the earlier expression from that
single replacement, and obtained the exact previously reviewed SHA-256. The
retained `Challenge.diff` therefore covers the entire byte difference. The
matrix argument is still the inverse of
`normSq x • (AᵀA) + normSq r • I`; the vector argument is still Aᵀr, and the outer
real dot product with Aᵀr is unchanged. All dimensions, quantifiers, assumptions,
other 16 statements and the rest of this theorem are unchanged.

The corrected explicit application expresses exactly the quadratic form
reviewed in the original mathematical approval. Definitions, numerical targets
and Comparator bytes were rehashed and remain identical to the approved inputs;
the hashes and exact replacement checks are retained in `CHECKS.json`.

This is an independent source-level approval of the correction. I have not
claimed a successful rerun based on the parent's operational message: the actual
Linux type check remains a separate gate whose final logs must be retained. No
local Lean/Lake execution or proof-body review occurred in this addendum.
