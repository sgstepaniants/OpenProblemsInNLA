# Exact IV03 source reuse

The files `NLA/IV03/Definitions.lean` and `NLA/IV03/Proof.lean` are copied
**unchanged** from Sidney Holden's Apache-2.0 formalization at
`sidneyholden1/OpenProblemsInNLA`, commit
`281f440650d174602120ca9b2b930d38f9fef205`, under
`intervals-and-absolute-value-equations/IV-03/lean/`.

| File | Original Git blob | SHA-256 |
|---|---|---|
| Definitions.lean | `5796205bb0cc77b542c76cd86a859241a3f2c67f` | `34d9726c54ec0b10005cb4225adf1c403a7109a0800b42c1f19865c1a897db2b` |
| Proof.lean | `99be5f1c6973761680b72e2c4514ce3c660793ea` | `8a6de76006c53aac4b9f37860b790bfe304ba25cf40aea5385daed376acc0272` |

Sidney Holden retains the formalization copyright and authorship. Matthew J.
Colbrook, Department of Applied Mathematics and Theoretical Physics,
University of Cambridge, retains the mathematical credit. Their source
comments are preserved, including the original development-stage description
in the definitions file. This project's `LICENSE` is byte-identical to the
original Apache-2.0 license (SHA-256
`cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30`).

The existing lemmas `zMatrix_maximum_principle`, `zMatrix_isUnit`, and
`zMatrix_inverse_nonnegative` are reused through small typed adapters in
`NLA/SF01/WeightedZReuse.lean`. They already prove the needed real Z-matrix
facts **given a positive weight**. They do not prove the new SF01 bridges
from and to the canonical spectral M definition; those obligations remain
separate. No other IV03 project source, proof acceptance or external result
is silently substituted for the SF01 target.

The new SF01 source is by George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology, with AI assistance.
That credit does not replace the reused formalization author. No contact
address is included. The two imported files depend only on one another and
the existing pinned Mathlib dependency. They will be recompiled with this
candidate batch; no new execution or proof acceptance is claimed here.
