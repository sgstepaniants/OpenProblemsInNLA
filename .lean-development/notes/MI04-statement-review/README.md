# MI-04 statement preparation

This private package contains the complete proposed statement boundary for the original universal positive-block operator-norm implication. It contains **21 independent Challenge obligations and definitions only**. No proof, statement approval, Lean elaboration, freeze or verified result is claimed. There is no Solution implementation yet.

Read [NUMERICAL_TARGETS.md](NUMERICAL_TARGETS.md) first, then [Definitions](NLA/MI04/Definitions.lean), [Challenge](Challenge.lean) and [SourceCorrespondence.md](SourceCorrespondence.md). The exact original statement and complete Colbrook source are retained under source/ at upstream ce47b5630bf3680d9211131c3a43825b022c139a. SOURCE-PROVENANCE.json binds their bytes.

The final target keeps every positive finite dimension, all complex matrices, every Hermitian A/B positive semidefinite completion, genuine Euclidean operator norms, and the actual affine-Hermitian conclusion. Singular matrices, repeated values and scalar matrices remain included. The original necessity implication is covered; the source's stronger four-way equivalence is not a proposed claim.

The intended proof uses a variational second-order sandwich with fixed spectral gap 1/2 and diagonal probes 1,0,1/2. Exact algebra replaces analytic eigenvalue branches. Normality and affine-spectrum reconstruction are full obligations, with pinned Mathlib's orthogonal joint-eigenspace APIs available for the normal diagonalization step. No proof is smuggled into an extra final hypothesis.

Original mathematics: **Matthew J. Colbrook**, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization: **George Stepaniants**, Department of Computing and Mathematical Sciences, California Institute of Technology. Substantial OpenAI Codex assistance is disclosed. No formalization-author contact email is supplied.

The package follows the shared Schiffer/Forsythe separation of statements and proofs, pinned LeanCert kernel trust, scoped Tau Ceti reviews and Comparator workflow. Lean 4.33.1 and all ten dependency revisions are pinned. Two independent statement reviews and actual non-root Linux elaboration must precede any proof implementation. The 21 deliberate placeholders belong only to Challenge, which Solution must never import. Final acceptance would require all LeanCert kernel assertions, transitive permitted-axiom checking, actual default-kernel replay and negative controls, two independent referees, and a separate publication review.

The live duplicate audit found no MI-04 Lean formalization on the 32 observed public upstream branch heads or open PR inventory. See duplicate-audit/DUPLICATE-AUDIT.json for exact scope and response hashes. This is a bounded dated check, not a claim about unlisted private repositories or future submissions.

No local Lean/Lake/cache process has been run. Schema validation of statement metadata does not satisfy the separate completed-project manifest/Comparator gates. No problem ID, canonical status or campaign count is changed by this draft.
