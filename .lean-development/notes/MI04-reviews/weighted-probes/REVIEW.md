# MI-04 independent incremental review: weighted probes and foundations

**Verdict: APPROVE the five complete source modules at the recorded bytes. No mathematical correction is requested.** Reviewer: independent nonimplementing OpenAI Codex agent `/root/next_matrix_functions`. This is an incremental mathematical source review, not a complete MI-04 approval or a report of Lean acceptance.

The new packet is `proof-handoffs/weighted-probes/MANIFEST.json`, SHA-256 `902f85eb65e7d0f1924c2257b330354bf75a43e2c9d296ea14d6c4e3736616fe`. I read its complete `WeightedProbes` and `Probes` implementations together with the required complete `Limit`, `BlockSymmetry` and `ScaledSymmetry` modules. Exact reviewed hashes are:

| Module | SHA-256 |
| --- | --- |
| Limit | `5a10598688c704f7ee2a13b990ee4cd9d35e2373ba051f651972a66e6aee6e1a` |
| BlockSymmetry | `7d5c0e711ba01a8bb98616427b50b06c64768e3bb12aef81ab06cd03720d3826` |
| ScaledSymmetry | `6ad9967e48602adc087ac905407f1554fc5e8fdb04f90dd9cea0605c8d350ef1` |
| WeightedProbes | `8fb7c11c6c36371a3a3cee2e3ed6869be8b325ea063a8abe35bd5cd79510f693` |
| Probes | `a5f2a00eb2ec5be139b866fbc5b2bde6007f40986115861883e062ccc680db87` |

The five corresponding advertised declarations have the exact frozen written signatures: `simple_peak_second_order`, `universal_to_extreme_symmetry`, `extreme_symmetry_scaled_unitary`, `weighted_magnitude_identity`, and `offDiagonal_magnitude_symmetry`. Section-instance elaboration and actual Comparator identity remain mechanical gates. Definitions, Challenge, numerical targets, source correspondence, provenance and pinned configuration retain their previously reviewed bytes. The earlier eight-module reviews, including the explicit Quadratic repair addendum, remain the foundation; none is silently replaced.

## Source fidelity and exact variational limit

I re-read the complete original MI-04 manuscript and the actual frozen Definitions/Challenge. The permanent original target is the necessity implication from the universal positive-block norm inequality to an affine-Hermitian representation. These five modules establish intermediate consequences needed by that implication. They do not claim the source's optional converse or the final representation, which still need their own implementation and review.

`spectralNorm` remains the actual complex Euclidean operator norm through `Matrix.toEuclideanCLM`. `topValue` remains the supremum over actual unit-vector real quadratic values; its attainment and spectral/positive-order bridges come from the reviewed variational modules. No substituted entry norm, assumed eigenpair or fixed-dimension approximation appears.

`Limit` uses the previously reviewed exact all-unit-vector sandwich. Every off-peak gap is at least one half, so each denominator of the finite upper coefficient tends to a nonzero value. Its numerator is fixed. The explicit lower Rayleigh quotient has numerator tending to the desired second coefficient and denominator tending to one. As positive epsilon tends to zero, the quantitative smallness condition holds eventually because the true operator norm is a fixed finite real value. The actual ordered-topology squeeze theorem then gives the advertised right-hand limit. I inspected that theorem's pinned source and the nontrivial-filter Hausdorff uniqueness API used later.

This proves exactly the necessary second-order coefficient without assuming an analytic eigenvector branch or a perturbation expansion. Negative or repeated off-peak diagonal entries are permitted. The only distinguished coordinate has diagonal value one and a uniform gap; no simple spectrum for the full matrix is imposed. A positive-side limit is sufficient for the later equality of limits, and it avoids any need to extend the scaling consequence to negative epsilon.

## From the universal norm property to pencil symmetry

`BlockSymmetry` constructs the actual block sign unitary and checks its conjugation identity with the displayed pencil. For any Hermitian T, let K be the pencil and c the actual top value of minus K. The two opposite diagonal coordinate vectors show c is nonnegative: their quadratic values are minus the real part and plus the real part of the same diagonal entry. This works in every positive dimension and avoids a separate trace argument.

The proved scalar-order bridge gives positive semidefiniteness of cI+K. Its diagonal blocks cI+T and cI−T are Hermitian and their sum is 2cI, so they satisfy the genuine universal completion premise. The actual positive-matrix norm bridge and scalar shift identity turn the norm inequality into `top(K) ≤ c`. Applying the same argument to −T and using the explicit sign unitary gives the opposite inequality. Thus `universal_to_extreme_symmetry` retains every Hermitian T and proves equality of the two actual extrema. It assumes neither invertibility of X nor positive definiteness of the completion.

`ScaledSymmetry` checks the inverse unitary action, a literal block diagonal unitary, and positive real homogeneity of the actual top value. For arbitrary Hermitian T after positive scaling, the proof evaluates the original hypothesis at T/r; r is explicitly positive, so its inverse and the Hermitian real scaling are legitimate. For unitary similarity, it evaluates the hypothesis at the inverse-conjugated Hermitian T and transports both extrema. These arguments preserve the universal quantifier rather than testing a selected class of diagonals.

## Weighted coefficient identity and entry isolation

`WeightedProbes` uses the genuine sum-type block coordinates. For a diagonal d with d_i=1 and all other d_j in [−1/2,1/2], `sumDiagonal d` is d in the upper block and −d in the lower block. It has a unique top value one at the upper i coordinate; its lower i coordinate is −1 and all other coordinates are at most one half. For `sumDiagonal (-d)`, the corresponding unique peak is the lower i coordinate. The perturbation is exactly the Hermitian zero-diagonal pencil with off-diagonal X and its adjoint, and the distinguished perturbation diagonal entries are zero.

I checked the row/column orientations explicitly. At the upper i peak, the lower-to-upper column of the perturbation contains conjugates of X's row entries; squared complex norms remove the conjugation. The denominator is 1+d_j, giving the weighted row sum. At the lower i peak for the opposite diagonal, the upper-to-lower column contains X's column entries with the same denominator, giving the weighted column sum. Both sums retain the common diagonal contribution with denominator two. No row/column index or conjugation is dropped.

For every positive epsilon, the full extreme-symmetry property for epsilon X and the actual block sign identity identify the two perturbed top values. Their normalized second-order functions are therefore eventually equal on the punctured positive neighborhood. The two independently derived right-hand limits must be equal because that real filter is nontrivial. This proves `weighted_magnitude_identity` at every allowed d, including both closed half-interval endpoints.

`Probes` then chooses d_j=0 away from i and a second diagonal differing only at a fixed distinct index j, where its value is one half. Both are genuine feasible probes. Their weighted sums differ by exactly q_j/3 for an arbitrary real coefficient family q: the weight changes from one to two thirds, while every other term cancels. Applying this symbolic finite-sum identity to the row and column squared norms isolates the desired equal entry magnitudes. When i=j the conclusion is reflexive; hence dimension one is explicitly covered and no distinct-index hypothesis is assumed in the final export. This is valid for every n and avoids dimension enumeration or differentiation in the diagonal parameters.

The restriction to the smaller half-interval is a proved sufficient probe family within the source's open (−1,1) domain. It supplies all coordinate probes needed for the original implication and matches the independently frozen numerical statements. It does not narrow the original universal block-norm hypothesis or final problem.

## Evidence, reuse and limitations

`INPUTS.json` binds the five new modules, all thirteen currently reviewed proof files, the complete source context, the frozen files and the read pinned APIs. I checked the exact five export headers, imports, absence of proof placeholders/new axioms/native execution, unchanged prior bytes, and actual original mathematical/formalization attribution. The sources use the established generic quadratic, unitary, positivity, finite-sum and topology APIs; the symbolic single-coordinate cancellation is a useful reduction of computation. All advertised new exports retain their LeanCert kernel assertions.

As a supplemental indexing check, `check_coefficients.py` uses only exact rational arithmetic to compare 21 small full-block peak coefficients with their explicit row/column sums and to check 70 one-coordinate probe differences. These finite diagnostics passed. They do not prove the general statements or any Lean acceptance.

No reviewed author file was edited, no local Lean/Lake command or cache download ran, and no successful build, transitive-axiom audit or Comparator result is inferred. The new weighted packet was not included in the then-running build. The remaining orthonormal-pair, normality, diagonalization, collinearity and final assembly exports are outside this incremental approval. Full-project independent review and canonical mechanical gates remain required. George's formalization credit, full Caltech CMS affiliation and no-contact-email preference remain respected; Matthew J. Colbrook's original Cambridge DAMTP mathematical credit is preserved.
