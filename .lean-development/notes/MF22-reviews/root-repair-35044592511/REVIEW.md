# MF-22 root independent repair addendum

**APPROVE the two exact proof edits at integrated manifest c0e84376.** This extends
my complete mathematical source review in the parent directory. I remain a
non-implementing MF-22 mathematical referee. Actual repaired compilation and all
canonical mechanical gates are pending; the previous run remains a failure.

I read the full repaired GreenEntryAlgebra and ProjectorAlgebra files, both
literal diffs, the actual failing diagnostics and the independent referee's
repair report. I also compared all 29 current source files against the Git bytes
of the failed run and my immutable original review. Exactly the two declared
one-line edits differ; all theorem and lemma headers remain identical.

The transfer decomposition lemma has roots only on its right-hand side. Giving
the existing rho and roots explicitly makes that already proved identity
available to simplification; it introduces no premise or alternate matrix. The
five-term Green expansion, both index cases and the boundary sandwich are
unchanged. The projector edit reduces the residual conditional with true guard
in the equal-index branch. The Lagrange evaluation argument and distinct-index
case are unchanged. Both repairs are mathematically valid and match the observed
compiler residuals. The other 27 source files and ten frozen boundary files are
byte-identical to their reviewed baselines.

This is a source-reconciliation approval, not a claim of successful Lean,
Comparator, kernel replay or axiom checks on these repaired bytes. There was no
local Lean/Lake execution, change of definitions or change of verification count.
Before publication, actual complete compilation, canonical controls, current
metadata and publication-commit reconciliation are still required.
