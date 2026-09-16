# IE-13 independent Origin/Front source review

**APPROVE the held two-module chunk.** No mathematical or concrete pinned-API correction is requested. This is an incremental source review of four additional frozen exports, not actual compilation or whole-problem verification. The exact Origin 07c87e38 and Front 563bd688 files and their full hashes are retained in CHECKS.json and MANIFEST.json.

I read both complete sources against the original IE-13 target/manuscript, the frozen definitions and four Challenge contracts. Every public signature matches exactly after whitespace normalization. All ten frozen inputs and the previously reviewed four-module prefix are unchanged. I independently matched the retained IE-14 Front source to its immutable Git version and inspected the reused generic swap/survivor identities. No cyclic support, two-row front, bound or witness result is imported.

The inverse-origin step is the actual physical swap composed with the previous inverse label map. The survivor equivalence says an original row is active after the step exactly when it was active before and is not the selected pivot label. This covers an identity swap too. Substituting the inverse-origin identities into the literal Schur update yields originalRow_update; the maximal-modulus pivot hypothesis yields its nonzero denominator and the complex multiplier bound. No real-entry or unique-tie assumption enters.

The front transition is exact set equality: the next old-label threshold `i < k+1+p` is the previous front threshold `i ≤ k+p`, while activity removes precisely the pivot label. This identity needs no band invariant.

Front jointly derives (a) at most p old surviving rows and (b) unchanged active rows whose original labels satisfy `i ≥ k+p`. Initially, the old labels inject into `range p`, and the input state is literal. At a later stage, a purported pivot label above k+p would be an unchanged row with original pivot-column entry zero by the lower band condition, contradicting pivot nonzeroness. Thus the chosen pivot belongs to the current front. Every future row at the next threshold has zero old pivot-column entry, is distinct from this pivot, survives, and has zero multiplier; its remaining entries stay unchanged.

For cardinality, the front is contained in old rows plus the unique label k+p when that label exists. Near the bottom there is no such label and the front is contained in the old rows. The selected pivot is actually in the front, so deleting it offsets the possible added row. The induction therefore retains the bound p. This argument includes p=0, q=0, all bottom stages and every admissible complex tie path. FutureRows is a proved internal invariant, never a hypothesis in the public front_structure theorem.

I inspected the pinned finite-set injection/cardinality/deletion APIs and swap identities with their exact arguments. The full signatures of originalRow_update, multiplier_bounds, front_transition and front_structure are unchanged, and kernel LeanCert checks remain present. No deliberate proof hole, new axiom, native-decide proof or author-file edit occurred.

Remote elaboration of these modules, the remaining IE-13 proof, complete independent reviews and canonical Comparator/kernel/negative-control gates remain pending. No local Lean or Lake was run and no verified count changed.
