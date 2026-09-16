# SF-01 spectral converse: root source review

Approve the exact four new modules in spectral-converse-03 for integration
with the separately reviewed two foundation repairs and the analytical bridge.
I am a nonauthor of this Lean implementation. I previously suggested the
finite-boundary route for the other, forward implication; that involvement
is disclosed and is not represented as fully independent original research.

I read all four new modules, their pre-implementation plan and author notes,
the frozen definitions and full 24-contract Challenge, and the relevant ranges
of all thirteen primary Mathlib files. I independently matched those APIs to
literal Git at the pinned commit. The actual source/contract checks executed
by the accompanying script preserve all seventeen original source hashes,
thirteen predecessor files and nine frozen inputs. Eight public headers match
the frozen contracts exactly. This static check is not Lean compilation.

The eigenvector bound uses actual complex spectrum transported through the
matrix/linear-map algebra equivalence. In finite dimension a spectral value
has a nonzero eigenvector. With positive weights, an attained maximum of the
coordinate norm-to-weight ratios bounds every coordinate. The maximizing
coordinate is nonzero, or the entire vector would be zero. Rowwise triangle
inequality and entrywise nonnegativity yield norm(mu)*norm(z_i) <= r*norm(z_i),
and the positive factor cancels. No eigenbasis, irreducibility, simple spectrum,
real-eigenvalue or symmetry assumption is introduced.

For a weighted Z-matrix, the maximum diagonal s gives B=sI-C >= 0. Positivity
of Cv makes each (Bv)_i/v_i strictly below s. Their finite attained maximum r
is also strictly below s. The complex eigenvector bound gives rho(B)<=r<s,
with the original representation C=sI-B. The argument proves the frozen
spectral M-matrix predicate rather than replacing it by a weighted definition.

For the H-matrix conclusion, positive comparison weights make A*diagonal(v)
strictly row diagonally dominant, including the absolute-value diagonal.
The pinned Gershgorin determinant result and determinant multiplicativity
give an actual unit A. This helper does not require a positive diagonal.
The earlier forward implication supplies the exact inverse-times-ones weight
and its equation from the original spectral H premise. The finite maxima
permit ties and dimension one, and no numerical sampling or interval search
is used. All new proof sources are free of holes and trust bypasses.

The original prefix closure be37db00... retains the two old foundation bodies
that failed in run 35090376438. Their separately reviewed repair packet selects
the two immutable after files; this review does not erase the old failure.
I found no required correction in the new spectral-converse mathematics.
The remaining sixteen contracts, the full Newton argument, two final whole-
source reviews, and actual default-kernel/Comparator/control and publication
checks are still required. No new Lean or Comparator execution is claimed.

Scoped Tau Ceti fidelity, nonvacuity, generality, proof-quality and attribution
checks were applied manually; its CLI was not run. The existing kernel
LeanCert half-positivity certificate remains the numerical ingredient.
Colbrook's mathematics and Holden's exact IV-03 reuse retain credit; George
Stepaniants, Caltech and his department remain credited without an email.
No accepted-count or publication-status change follows from this review.
