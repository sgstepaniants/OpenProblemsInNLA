# SF-01 spectral converse: independent source review

Approve the four new modules in author packet `spectral-converse-03` for the
next coordinated Linux development build, together with the separately reviewed
foundation repairs. I found no required correction in these four modules.
This is source and mathematical approval, not a Lean execution result or a
verification of the complete SF-01 problem.

I am `/root/mi04_independent_referee`, a nonauthor of this SF-01 source. I read
all 265 lines of WeightedSpectrum, SpectralMConverse, HWeight and
SpectralBridgeChecks, the four preceding analytical bridge modules, the actual
spectral definitions and Spectrum module, all 24 frozen contracts, and the
numerical obligations. This continues my retained original-target, manuscript
and complete foundation review. Both independent analytical-bridge reviews are
also retained and bound. I did not run Lean, Lake, Comparator, a cache command,
or the Tau Ceti CLI; its relevant fidelity, correctness, generality, reuse,
proof-quality and attribution standards were applied manually.

The spectral argument uses genuine complex spectrum and an actual nonzero
complex eigenvector. The matrix-to-linear-map algebra equivalence preserves
the spectrum; finite dimension supplies the eigenvector. For a positive weight
v, the proof chooses an attained maximum of `norm(z_i) / v_i`. Its selected
coordinate is nonzero, since otherwise the maximum bounds every coordinate by
zero, contradicting the nonzero eigenvector. Entrywise nonnegativity gives the
row norm estimate. The assumed row bound `B v <= r v` then gives
`norm(mu) * norm(z_i) <= r * norm(z_i)` and permits cancellation of a strictly
positive factor. No normality, diagonalizability, positive entries, irreducibility,
distinct eigenvalues or real-spectrum assumption enters this proof.

For the Z-matrix converse, s is the attained maximum diagonal of C and
`B = s I - C` is proved entrywise nonnegative. Positivity of C v gives every
ratio `(B v)_i / v_i < s`; the finite maximum r of these ratios still satisfies
`r < s`. The preceding complex spectral estimate bounds every spectral modulus
by r. The existing genuine spectral-radius theorem gives `rho(B) < s`, with
the exact original representation `C = s I - B`. This proves the frozen
`weighted_Z_spectralM` contract; it does not introduce the desired conclusion
as a definition or substitute a matrix norm for the spectral radius.

For HWeight, the comparison row identity is the actual diagonal absolute-value
term minus the sum of off-diagonal absolute-value terms. A positive comparison
weight makes `A * diagonal(v)` strictly row diagonally dominant. The actual
Gershgorin determinant theorem proves its determinant is nonzero, and determinant
multiplicativity proves A is a unit. The preceding analytical bridge supplies
the particular positive vector `comparison(A)^-1 * 1` from the original spectral
H-matrix premise. Thus the frozen `H_positive_weight` conclusion obtains an
actual inverse and its exact equation, without assuming inverse positivity or
the existence of a suitable weight. The root-namespace Gershgorin API and its
finite-index assumptions were checked directly.

The maximum arguments include ties, repeated eigenvalues, zero entries and
dimension one. The original n >= 1 premise supplies nonemptiness exactly where
needed. The determinant helper also permits the empty-dimensional case under
its own stated premises. The spectrum reasoning covers arbitrary finite complex
eigenvectors and arbitrary nonsymmetric real matrices. Strict inequalities are
preserved by attained finite maxima; no limiting or sampled argument is used.

The independent static audit passed 295 checks. It authenticated all 15 packet
entries and 80 external bindings, all 17 source hashes and closed local imports,
the 13 unchanged predecessor sources, nine frozen inputs and all 24 contracts.
The two new public headers match exactly; eight public contracts now have source
implementations. All 13 cited Mathlib API files were compared with literal Git
blobs at `0df444a360eaa60ab8c11dca51a86af692955474`, and their relevant signatures
were read. The new modules add no holes, custom axioms, native evaluation bypass,
resource-limit increase or numerical interval enumeration. Their kernel/axiom
commands are requests for the future build, not evidence of execution. The
earlier LeanCert half-positivity certificate remains the numerical ingredient;
no new numerical obligation was hidden in this spectral bridge.

The original sealed prefix closure is
`be37db00f1cc2bca65d4c7abe4f3dea4b668173304bdfa582de5d2495ce83526`.
It intentionally retains the old Complexification and Numerical foundation
bodies that failed in actual run 35090376438. Their separately reviewed repair
closure is `aab365c85c8afbd291212358548bc06bca1a130a8b6ce2c9a1d279e5f7414ee7`.
My audit reconciles both maps and confirms that only those two earlier bodies
differ, with these four new modules unchanged. This review does not erase that
actual failure or assert that either complete prefix has compiled.

Sixteen frozen contracts remain unfinished: the shift/comparison/resolvent
steps, ridge preservation and commutation, pole positivity and diagonalization,
residue normalization, reciprocal weights and blocks, matrix reciprocal identity,
Newton data step, first iterate, representation of every iterate, and the full
canonical Newton preservation theorem. Consequently SF-01 is not complete.
Its final full-source reviews and actual kernel, Comparator and control runs
remain required before any verification claim or count change.

Matthew J. Colbrook's mathematics, Sidney Holden's unchanged Apache-licensed
IV-03 reuse, and George Stepaniants's name, Caltech and department affiliation
remain credited. The new modules contain no email addresses. No source, Git
state, build metadata, publication status or accepted count was changed.
