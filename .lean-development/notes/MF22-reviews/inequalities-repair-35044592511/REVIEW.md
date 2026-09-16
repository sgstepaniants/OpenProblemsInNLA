# MF-22 independent proof-repair reconciliation

**APPROVE both exact proof-only changes.** The complete mathematical source
approval in `MF22-inequalities-final/REVIEW.md` extends to this two-file revision.
Reviewer: OpenAI Codex agent `/root/next_inequalities`, still a non-implementing
MF-22 referee. This is source approval only, with repaired full-graph compilation
and all canonical gates pending. The failed actual run remains failed.

I inspected the actual errors in run 35044592511 at
`cc17d70a568de50bb428f2665f576aec9dcd884e`, both complete affected theorem bodies,
their exact original/current diffs and all 29 current source identities against
my prior immutable review. Exactly two one-line proof edits occurred.

In `GreenEntryAlgebra.green_expansion_of_sandwich`, the existing proved power
decomposition is now explicitly instantiated at rho and the chosen roots before
simplification. The old left-hand side contains no roots, so a bare simp lemma
cannot infer that parameter; the actual log marks it unused and leaves unmatched
transfer powers. Supplying the existing variables changes no identity or premise.
The exact five-term expansion and full projector sandwich remain identical.

In `ProjectorAlgebra.spectralProjector_mul_of_charpoly`, `ite_true` reduces the
remaining `if True then Pi else 0` in the equal-index case. The actual log displays
precisely that residual goal. The Lagrange polynomial identity, its evaluation,
and the distinct-index branch remain unchanged.

All other 27 source files and all ten frozen mathematical/configuration boundary
files match the previous review. No theorem signature, hypothesis, definition,
import or trust policy changed. `CHECKS.json` binds both source revisions and the
authentic diagnostic log; retained before/after files and diffs make the scope
reviewable. No local Lean command, source mutation or verification-count change
was performed by this referee. Acceptance still requires the repaired actual
Linux graph followed by independent canonical Comparator/default-kernel/control
evidence and final source reconciliation.
