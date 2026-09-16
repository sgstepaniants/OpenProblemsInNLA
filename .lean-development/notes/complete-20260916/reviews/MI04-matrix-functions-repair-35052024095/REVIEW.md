# Independent MI-04 observed-repair addendum

**APPROVE at source level.** This extends my complete nonimplementing MI-04 review and the previous Limit repair addendum. I read the complete repaired `WeightedProbes.lean`, the exact two-line diff, the authentic full MI-04 compiler log, the pinned `neg_ite`/diagonal definitions and the current closure. I did not edit author sources or invoke Lean/Lake.

The two additions of `neg_ite` are precisely matched to the logged goals at lines 26 and 32: distributing negation across an `if i = j` diagonal entry. The pinned lemma states `-(if P then b else c) = if P then -b else -c`, proved by propositional case split and reflexivity. The existing simplifier then reduces `-0`. It changes neither the opposite diagonal matrix, the block matrix, the weighted row/column coefficient identity nor any quantifier or hypothesis. The complete file still derives the identity from the actual second-order one-sided limit and extreme spectral symmetry, for every dimension and each admissible peak diagonal.

The reviewed repair packet is `5787a22e4421a0c326bf363d227f151913d20b6f94f3dea19ce6dd07fd6feae7`. The repaired file is `e72d7cd3a10c574477a794d26aba66d40da7486c9ead38e9e4e1d31840570eea`; the final 21-source closure is `6f0865308ec97f9052f862e54a94ca4c439ca426742d88ab617c267a841d9ddc`.

Independently checked all 21 prior sources against actual Git `93abf01922d103993f2a92e819f207d63effbfae`, their earlier reviewed hashes, and every command's pre/post receipt maps. The new closure differs only in the two explicit simp arguments. All other 20 sources, all helper/public headers and all 10 frozen files are unchanged. The API snapshots match pinned Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

Actual Linux run `35052024095` accepts the preceding Limit repair and prints the standard three axioms for `simple_peak_second_order`. It fails at these two WeightedProbes helper reductions, followed by the expected trust rejection of the dependent export. The later graph and the corrected file have **not** passed in that run; neither a complete MI-04 development pass nor Comparator/canonical verification is claimed. The root's 1,118-input operational audit is retained separately from this mathematical source review.

`CHECKS.json` records the exact checks and source/frozen maps. `reviewed-source/` retains all current files as text archives, and `evidence/` preserves the real failed run and exact submitted repair without replacing earlier review history. No mathematical correction is requested.
