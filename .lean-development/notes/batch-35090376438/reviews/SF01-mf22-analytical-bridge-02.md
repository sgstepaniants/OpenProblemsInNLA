# SF-01 analytical bridge: independent scoped source approval

Reviewer: `/root/mf22_publication_referee`, a nonauthor of the SF-01 code. I author unrelated MF-07 and RA-02 work. This is a manual mathematical and source review applying the relevant Tau Ceti rubrics; I did not run the Tau Ceti CLI, Lean, Lake, Comparator, or a cache command.

**Approve the exact four-file, 222-line analytical bridge for a subsequent coordinated Linux build.** Its author manifest is `9991accd83b41e0ae0284b43c3cf589af9507bcb3da1d9a0ae3205da13223e65`; its complete 13-file prefix closure is `35953c4182c7ab20e1e49fae0f337708b0b9680b0539c843dc0f2f955fa80122`. No required source correction was found. This is not a compilation result or verification of the full SF-01 problem.

## Review scope and fidelity

I read all 13 sources in that prefix, including the complete credited IV-03 reuse, the actual spectral definitions, the earlier complex-spectrum/homotopy argument, and the four new modules. I also read the complete original canonical target and retained manuscript at upstream `ce47b5630bf3680d9211131c3a43825b022c139a`, all 24 frozen Challenge statements, the source correspondence, and the author plan and audit. The manuscript's stronger extensions are not being substituted for the frozen Newton target.

The new public header `spectralM_positive_weight` exactly matches Challenge. It derives that the particular vector `C⁻¹ *ᵥ 1` is strictly positive, together with the actual inverse equation, from the original spectral M-matrix premise. It does not assume a positive weight, an equivalent M-matrix characterization, or inverse positivity. The new helper hypotheses are discharged when forming this public conclusion.

## Mathematical checks

`UnitWeightContinuity` obtains the inverse equation from the actual matrix nonsingular inverse and unit determinant. Inverse continuity uses the pinned determinant/inverse theorem at a genuinely invertible matrix; composition with multiplication by the all-ones vector gives continuity of the specific weight. The homotopy is the actual matrix `s I − t B`. Its initial weight is positive because `s > 0`, which follows from the nonnegative genuine spectral radius and the strict spectral bound.

The boundary contradiction is exact: if a homotopy solution is coordinatewise nonnegative and its coordinate `i` is zero, nonnegativity of `B` and `t` makes the `i`th coordinate of `(s I − t B)v` nonpositive. That contradicts the equation that this coordinate equals one. There is no assumption that all intermediate solutions are already positive.

`PositivePath` uses a continuous finite maximum `g(t) = max_i (−w(t)_i)`. Nonemptiness follows from the original `n ≥ 1`. At zero, every coordinate is positive, so the attained maximum is negative. A hypothetical nonpositive coordinate at any `t ∈ [0,1]` makes `g(t) ≥ 0`. The intermediate value theorem on `[0,t]` supplies a point where `g = 0`; every coordinate is then nonnegative and the attained maximum identifies a zero coordinate. The proved boundary exclusion gives the contradiction. The argument includes both endpoints, repeated coordinates, arbitrary finite dimension, and a potentially nonmonotone path. It needs no first-crossing choice.

`SpectralMWeight` applies that result to the actual inverse weights, using the earlier actual spectral homotopy unit theorem for every parameter. At `t = 1` it recovers the supplied matrix `C`; the Z-matrix sign property follows directly from the same representation. I checked the earlier homotopy spectral reasoning as part of the complete prefix read, rather than treating its theorem name as an unexplained surrogate premise.

## Source, API, and trust checks

My separate audit independently verified all 19 entries of the new packet, all 18 entries of the prior foundation packet, every author source-binding record, the nine unchanged earlier sources, the nine frozen files, the exact 13-source import closure, and all six currently present public headers against their frozen contracts. It authenticated all 11 cited primary API files directly from pinned Mathlib Git commit `0df444a360eaa60ab8c11dca51a86af692955474`, including the actual finite-supremum attainment/continuity and intermediate-value signatures. I also inspected the actual `Matrix.mul_nonsing_inv` signature. Source safeguards found no holes, custom axioms, native trust, imported Challenge, resource-limit increase, or changed numerical boundary in this prefix.

The earlier LeanCert half-positivity certificate and its consumer remain unchanged. The new modules add no numerical interval computation. The new checking module requests default-kernel trust and axiom reports; the presence of those commands is not evidence that they have executed.

Scoped Tau Ceti correctness, generality, proof-quality, reuse, and attribution checks are satisfied. The original spectral target has no added restriction, the analytic proof uses the existing Mathlib inverse/continuity/finite-extremum/IVT APIs, and the project-specific bridge helpers have actual consumers. Targeted searches in the pinned topology/order and matrix libraries did not identify a direct replacement for the positive-coordinate boundary argument or this spectral M-matrix bridge. This bounded search is not a claim to exhaustive theorem discovery. Matthew J. Colbrook's mathematics, Sidney Holden's unchanged IV-03 formalization, and George Stepaniants's new formalization and Caltech department affiliation remain credited. The four new sources contain no email addresses.

## Limits and retained preparation history

Four newer private files appeared while this review was running: `HWeight`, `SpectralBridgeChecks`, `SpectralMConverse`, and `WeightedSpectrum`. They are outside this immutable 13-file handoff and outside this approval. My first static inventory attempt rejected the overly broad assumption that the private directory contained only the sealed prefix. I retained that script and failure explanation, then narrowed the audit to the exact sealed prefix and checked that all its local imports stay within it. No source hash failure occurred and no author source or packet was altered.

This prefix contains candidate proofs of six of the 24 frozen public contracts; the other 18, the full `Solution`, a complete Linux build, final default-kernel/Comparator controls, and final whole-source referees remain pending. The current combined run excludes this new bridge. This review changes no problem status, publication status, or accepted count.
