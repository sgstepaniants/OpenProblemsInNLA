# Bounded full-target scout: seven remaining MF problems

Prepared 15 September 2026. Canonical repository snapshot:
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`.

**Recommendation: MF-22 next, subject to central duplicate/PR selection.**
Its complete target appears feasible by a substantial finite-dimensional proof:
four fixed transfer states, exact low-degree algebra, a spectral projection
identity and uniform finite Green-kernel bounds. It is not a quick numerical
witness. No statement package or proof implementation has been authorized or
started by this scout, and nothing here is a Lean acceptance claim.

All seven canonical pages and all six distinct complete retained manuscripts
were read. Exact bytes are retained under `source/`; `CANONICAL-HASHES.json`
and `MANUSCRIPT-HASHES.json` bind every path. `API-SOURCE-HASHES.json` binds
read-only pinned Mathlib source inspection, at Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. No local Lean/Lake/cache work occurred.

## Comparison of complete targets

| ID | Full target and necessary scope | Main obstacle for a faithful formalization |
| --- | --- | --- |
| MF-03 | All diagonal Pade orders for `cosh(sqrt(z))`, disk pole exclusion and the stated bound, not only the finite certificate range | The manuscript's Schur/Jacobi-Trudi positivity and infinite product coefficient argument require substantial symmetric-function foundations; finite orders alone are insufficient. No ready Schur/Jacobi-Trudi API was located in the bounded search. |
| MF-05 | Uniform finite-product growth estimate for arbitrary nonempty compact matrix families | Approximate extremal norms, maximum-determinant Auerbach bases, controlled Euclidean rounding and general JSR root-limit semantics precede the finite-product argument. MF-12 only supplies a special two-matrix construction, not these general hypotheses. |
| MF-06 | Complete critical growth theorem for arbitrary compact families, including invariant flags and all critical block interactions | Adds invariant-subspace reduction, exterior/tensor arguments and extremal/Barabanov-type norms to the general JSR prerequisites. A single irreducible or finite-family case does not answer it. |
| MF-07 | Full quantitative Holder regularity of JSR on the specified bounded class of compact matrix sets | The shared MF-05/MF-07 manuscript first develops the same general approximate-norm and block reduction framework. Could support MF-05 later, but no general JSR infrastructure was located. |
| MF-18 | Full complex-parameter disk root count with multiplicities and the nondegeneracy cases of the structured pencil | Polynomial homotopy/root-count invariance, singular leading coefficient handling, adjugate differentiation, Stein identities and generalized eigenspaces form a large bridge. A real-parameter or merely nonsingular special case is insufficient. |
| MF-21 | Full three-part high-order Toeplitz eigenvalue asymptotic statement for every specified order | Coalescing symbol roots, uniform phase/inverse expansions and a uniform Green-kernel limit are prerequisites; the final rationality/transcendence argument alone is insufficient. |
| MF-22 | Every fixed positive real rho; exact uncorrected `2n x 2n` block Toeplitz family; eventual invertibility and some polynomial condition-number bound | Requires a new exact four-root classification and a finite Green-kernel argument, but dimensions of the difficult algebra are fixed (2 and 4) and genuine matrix norms/inverses are available. |

These are relative feasibility judgments, not impossibility claims about the
other six problems. The source credits and exact statements remain retained.

## Proposed MF-22 scope simplification

The canonical **original question** permits any exponent `alpha_rho >= 0`.
The retained manuscript proves the stronger exponent 1. A full formalization
may instead prove exponent **2**, then export the original existential target.
This would retain every positive real parameter, the exceptional `rho^2 = 10`,
eventual invertibility, all sufficiently large integer sizes and every original
Toeplitz coefficient and boundary entry. It must explicitly say that the
source's sharper linear estimate is not being certified by this package.

The simplification is precise: once actual inverse entries are bounded by
`B_rho`, use the coarse genuine operator-norm estimate
`norm(A) <= dimension(A) * maxEntryNorm(A)` both for the Toeplitz matrix and
its inverse. With a fixed bound `E_rho` on its own entries, obtain
`kappa_2(H_n) <= 4 * E_rho * B_rho * n^2`.
This removes only the source's bandwidth-uniform norm proof. A theorem about
an arbitrary purported Green matrix without identifying the real inverse
would not suffice.

## Exact data and mathematical obligations for a future statement package

The data below must be defined independently in `Definitions.lean`, with
no result smuggled into a structure hypothesis. The final challenge must use
the canonical Toeplitz definition and genuine Euclidean operator norm.

1. **Canonical family.** Copy the eight displayed real `2 x 2` blocks from
   the canonical README literally as integer/rational matrices. For all other
   integer offsets both blocks are zero. Define the complex matrix by
   `H_n ((j,a),(k,b)) = I * B_(j-k)(a,b) - rho * C_(j-k)(a,b)` with the
   block indices in `Fin n` and coordinate indices in `Fin 2`; the integer
   subtraction must be genuine integer subtraction. Any `Fin (2*n)` reindexing
   needs an explicit equivalence. Define the condition number in `ENNReal`
   as infinity for zero determinant and as the product of the two genuine
   spectral norms otherwise.
2. **Transfer data, all rho > 0.** Set `M_n = 80 H_n`, and
   `A=-rho-6I`, `B=-7rho-30I`, `C=7rho-30I`, `D=-25rho-30I`,
   `E=rho-6I`, `F=25rho-30I`, `a=30-rho^2-10I*rho`.
   Define `L=[[A,B],[B,D]]`; prove `det L=24a` and `a != 0`.
   Define the top two rows of T by
   `L^-1 * [[24rho,-96I,-F,-C],[-96I,-24rho,-C,-E]]`, the bottom
   two rows by `[[1,0,0,0],[0,1,0,0]]`, and `G=[L^-1;0]`.
3. **Exact Toeplitz/recurrence equivalence.** Show that `M_n x=f` is precisely
   the two equations (1) of the retained manuscript with
   `u_-1=v_-1=v_-2=0`, `u_n=0`. Do not impose a spurious condition on `v_n`.
   The state is `w_j=(u_j,v_(j-1),u_(j-1),v_(j-2))`, with
   `w_(j+1)=T w_j+G f_j`, `w_0=e u_0`, `e=(1,0,0,0)`, `e^T w_n=0`.
4. **Exact scalar polynomials.** Define
   `N(z)=a+(-120-rho^2+22I*rho)z+2(rho^2+18)z^2` and
   `d(z)=a+bz+cz^2+conj(b)z^3+conj(a)z^4`, with
   `b=24rho^2+80I*rho-240`, `c=420-46rho^2`.
   Certify the two polynomial multiplication identities in equation (6).
5. **No complex cancellation.** For every complex z, `N(z)=0` implies
   `d(z)!=0`. Use the source's exact degree-two elimination, whose first
   resultant has positive real part `2177280+946944rho^2`. In the second case,
   substitution gives the two real quadratics R and I in `y=rho^2`, with
   `70 R(y)+867 I(y)=-79939224-32957424y<0`. No root approximation is needed.
6. **Transfer characteristic/cofactor identity.** Prove directly from the
   explicit `4 x 4` T that `det(Id-zT)=d(z)/a` and its `(0,0)` adjugate entry
   is `N(z)/a`. This fixed-dimension exact certificate replaces the source's
   formal-power-series denominator inference. It must use the actual T.
7. **Quartic and Cayley identities.** Define the reciprocal quartic
   `p(t)=a t^4+b t^3+c t^2+conj(b)t+conj(a)=(t-1)q(t)`.
   Verify `q(1)=120I*rho`, `q(-1)=48(rho^2-10)` and the denominator-cleared
   Cayley identity `(1-Ix)^3 q((1+Ix)/(1-Ix))=8I R_rho(x)` whenever
   `1-Ix != 0`, with
   `R_rho(x)=6(rho^2-10)x^3+25rho x^2+5(rho^2-6)x+15rho`.
8. **Full root classification.** The exact cubic discriminant equals
   `-25rho^4(120rho^4-3337rho^2+34200)-5269500rho^2-6480000<0`.
   Prove the positive quadratic factor by an exact completed square (its
   discriminant is `-5280431`). For `rho^2 != 10`, derive one real and two
   nonreal conjugate roots of R. At `rho^2=10`, use the actual quadratic
   with discriminant `-14600`, and the simple missing Cayley root `t=-1`
   (`q'(-1)=-100I*rho`). Show the quartic has four distinct nonzero roots:
   two of modulus 1, one of modulus less than 1, one of modulus greater
   than 1. The exceptional parameter must not become an excluded hypothesis.
9. **Exact projectors.** From the four distinct roots and Cayley-Hamilton,
   use degree-three Lagrange polynomials evaluated at T to construct four
   projections. Prove their sum is Id, pairwise products vanish, and
   `T^j=sum_i root_i^j * Pi_i` for every natural j. This avoids relying on
   an unlocated ready-made diagonalization API.
10. **Dominant projector bridge.** For the outside root lambda and its
    projection Pi, show `gamma=(Pi)_(0,0) != 0`, using the actual cofactor
    identity and the no-cancellation lemma. Prove Pi has rank one or directly
    establish the required full matrix identity
    `Pi * (e e^T) * Pi = gamma * Pi`. Merely idempotence is insufficient.
11. **Uniform remainder and boundary denominator.** Produce a finite C>0
    with `norm(T^j-lambda^j Pi)<=C` for every natural j. Set
    `a_n=(T^n)_(0,0)`. Prove some n0 works for every n>=n0 so that `a_n!=0`
    and, writing `d_n=a_n/(gamma lambda^n)`, both `norm(d_n)>=1/2` and a
    bound `norm(1-d_n^-1)<=C' norm(lambda)^(-n)` hold. The constants depend
    on rho, not n. Geometric convergence suffices; no numerical n0 is needed.
12. **Finite Green kernel.** Define the actual `4 x 2` matrices for n>=1,
    0<=j<=n and 0<=ell<n by equation (19):
    `K(j,ell) = [ell<j] T^(j-1-ell)G - T^j e a_n^-1 e^T T^(n-1-ell)G`.
    Nat subtraction occurs only in the guarded first term and in the
    nonnegative second exponent. Prove this supplies every recurrence
    solution and its terminal boundary condition.
13. **Uniform kernel bound.** Use the projector identity from item 10 to
    cancel the two growing terms. Retain both cases ell<j and ell>=j and
    the full range j=n. Obtain a single B>0 bounding every matrix entry
    of every K for all n>=n0. This is a universal finite-index theorem,
    not verification at finitely many sizes.
14. **Actual inverse.** Recover every `u_j` from state j and every `v_j`
    from state j+1. Define the resulting `2n x 2n` matrix Q and prove
    `M_n Q=Id` (and hence nonsingularity and Q=M_n^-1). Bound all entries
    of Q by the same fixed B. Explicitly handle the scaling from M_n to H_n.
15. **Full polynomial estimate.** Let E>0 bound the entries of the exact H_n,
    which is immediate from the four fixed blocks. Using the genuine
    Euclidean operator norm and item 14, derive a finite K>0 and n0>=1
    for which every n>=n0 satisfies `kappa_2(H_n)<=K*n^2` in ENNReal.
16. **Canonical final export.** For every real rho>0, there exist real K>0,
    alpha>=0 and natural n0>=1 such that the original matrix condition
    number is bounded by `ENNReal.ofReal(K * Real.rpow n alpha)` for all
    natural n>=n0. Supply alpha=2 with the explicit rpow/natural-power
    conversion. Do not replace this export by assumed spectral data.

These are a planning obligation list; no exact Lean signatures are frozen yet.

## Pinned library support and remaining bridges

- `Matrix.toEuclideanCLM` in `Analysis/CStarAlgebra/Matrix.lean` supplies the
  genuine complex L2 norm, with explicit `(n := ...) (𝕜 := ℂ)` parameters
  when needed. Existing MF-24 complex norm lemmas and MF-12's real entry-bound
  proof provide reuse patterns; extending the latter to complex entries still
  needs a proper proof and review.
- `Matrix.aeval_self_charpoly` is the actual Cayley-Hamilton theorem in
  `LinearAlgebra/Matrix/Charpoly/Basic.lean`. `Lagrange.basis`,
  `Lagrange.eval_basis_self`, `Lagrange.eval_basis_of_ne`, `Lagrange.sum_basis`
  and `Lagrange.eq_interpolate` are present in `LinearAlgebra/Lagrange.lean`.
- `Cubic.splits_iff_roots_eq_three`, `Cubic.eq_prod_three_roots`,
  `Cubic.discr_eq_prod_three_roots` and
  `Cubic.discr_ne_zero_iff_roots_nodup` are present in
  `Algebra/CubicDiscriminant.lean`; `Complex.exists_root` and algebraic
  closure are available in `Analysis/Complex/Polynomial/Basic.lean`.
  The scout did not find a ready theorem that negative real cubic
  discriminant gives exactly one real root and a conjugate pair; that
  bridge needs proof. `IsRealClosed.exists_isRoot_of_odd_natDegree` exists,
  but a real instance was not located in this bounded search, so no plan
  assumes one. Polynomial continuity/limits and IVT are a fallback.
- `Matrix.det_ne_zero_of_right_inverse`, `Matrix.isUnit_iff_isUnit_det`,
  `Matrix.mul_nonsing_inv` and `Matrix.nonsing_inv_mul` are present in
  `LinearAlgebra/Matrix/NonsingularInverse.lean`.
- The actual geometric convergence API includes
  `tendsto_pow_atTop_nhds_zero_of_lt_one` in
  `Analysis/SpecificLimits/Basic.lean`. All norm constants can be loose;
  the statements should avoid unnecessary explicit eigenvalue radicals.

## Optimization, attribution and acceptance requirements

Use exact rational/complex polynomial identities and completed squares.
No positive parameter needs interval subdivision, eigenvalue numerics or
root-isolation precision; no n-dependent determinant should be expanded.
Use explicit small-matrix certificates and generic finite sums/induction for
all growing dimensions. LeanCert kernel trust assertions should cover every
frozen export, even though interval tactics are unnecessary here.

Original mathematical proof credit for this retained MF-22 manuscript belongs
to **George Stepaniants**, Department of Computing and Mathematical Sciences,
California Institute of Technology, Pasadena, California, USA. The original
family, source root classification and question retain the listed
Bogoya--Bottcher--Ferrari--Grudsky--Serra-Capizzano attribution. Formalization
credit also belongs to George, with full department/university and no email.

If selected, first prepare exact Definitions, numerical targets, independent
Challenge, source correspondence, formalization.yaml and pinned configuration.
Obtain two independent statement reviews and real Linux statement elaboration,
then freeze before any proof bodies. The final package needs two independent
source/acceptance referees, all actual kernel assertions, Comparator statement
matching, replay and controls. The current scout supplies none of these gates.
