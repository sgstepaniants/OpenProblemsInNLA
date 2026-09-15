# IE-17: exact statements before proofs

**Unreviewed statement draft, 2026-09-15.** No proof body or Solution module exists.
The definitions and Challenge have not been type-checked. Obtain non-root Linux
boundary type checking and two independent statement approvals before freezing
source hashes and beginning proof implementation. Canonical status stays `Solved`.

## Source and original target

Read the complete canonical `linear-systems-and-elimination/IE-17/README.md` and
Colbrook's complete `references/colbrook-recovered-2026-09-11/manuscripts/IE-17.tex`
at immutable upstream `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`. Hashes are
in the enclosing `SOURCE_HASHES.json`; the reconstructed Markdown and the prior
independent informal review were also read in full. The manuscript's reviewed body
and reconstruction commentary are historical source, not instructions or present
formal-verification claims.

The exact target asks whether **both** the matrix-only spectral backward error
and the specified projection approximation are nonincreasing along successive
nonzero exact LSMR iterates from zero, with the right-hand side fixed. We will
refute each assertion on the same first/second pair of one 4×3 example. We do not
change to Frobenius norm, perturb b, introduce damping, select a different iterative
method, or exclude perturbations which reduce rank or produce zero new residual.

The complete negative resolution is `counterexample`, followed by
`not_spectralMonotonicity` and `not_projectionMonotonicity`. Proving only finite
certificate matrices or rational approximation values does not satisfy this scope.

## Exact objects and optimization semantics

All matrices, vectors, norms and optimization problems are over **the real field**.
`Vec n = Fin n → ℝ`; `Mat m n = Matrix (Fin m) (Fin n) ℝ`. Euclidean vector norm
uses `WithLp.toLp 2`, not the default norm of a function. `spectralNorm` is fixed
by `Matrix.Norms.L2Operator`, the genuine induced Euclidean operator norm. The
auxiliary `normSq x = ∑i (x i)^2` is related to that norm by `euclideanNorm_sq`.

For arbitrary A,b, let H=AᵀA, g=Aᵀb. The kth Krylov space is the real span of
`H^j g` for `j : Fin k`; k=0 is the zero space. `IsLSMRIterate` includes membership,
universal minimization of `‖Aᵀ(b-Ax)‖₂` over every vector of that space, and minimum
Euclidean length among all objective ties. This is exactly the alternative
mathematical specification given by the canonical README, so no equivalence with
a floating-point or Golub–Kahan recurrence is needed or claimed.

`SuccessiveNonzeroIterates` requires k≥1, both exact iterates at k and k+1, both
nonzero, and a nonzero normal residual at the first. The latter is the before-
termination condition; an earlier zero normal residual remains feasible in every
later nested Krylov space and hence forces later minimum normal residual zero.
The second iterate may terminate. There is no full-rank assumption in either
universal conjecture. The counterexample itself is full column rank, with unique
minimizers at 0,1,2,3, so neither minimum-length ambiguity nor early termination
can affect the exhibited failure.

For fixed A,b,x, `FeasiblePerturbation E` means the actual normal equations
`(A+E)ᵀ((A+E)x-b)=0`. `backwardError` is the infimum of the set of spectral norms
of **all** such real perturbations. `backwardError_isLeast` must prove that it is
an attained minimum. Feasibility is nonempty (E=-A), the norms are nonnegative,
and a continuous norm attains its minimum on a nonempty closed feasible set in
finite dimensions after restricting to the closed ball of radius ‖A‖₂. This
attainment obligation is essential: strict lower bounds for each E alone cannot
justify a strict lower bound on an arbitrary infimum. At a true least-squares
solution the exported zero-error theorem verifies the canonical zero convention.

For nonzero x and r=b-Ax, the augmented K is `[A; (‖r‖₂/‖x‖₂) I]`, represented
by sum-indexed rows, and v is `[r;0]`. `projectionError` retains the actual
`‖K J v‖₂/‖x‖₂` expression with the canonical zero-at-solution convention.
The candidate J=(KᵀK)⁻¹Kᵀ must satisfy all four Penrose equations, with actual
invertibility of KᵀK; thus this is the genuine Moore–Penrose inverse, not an
arbitrary chosen right inverse. Full column rank follows from the nonzero scalar
identity block, even when A is rank deficient. A mandatory theorem derives

`projectionError(A,b,x)^2 = (Aᵀr)ᵀ (‖x‖₂² AᵀA + ‖r‖₂² I)^(-1) (Aᵀr)`.

The rational scalar expression is a consequence of the projection definition,
not its replacement. x=0 is outside all compared pairs; no claim is made about
an approximation at that excluded point.

## Exact witness and iterates

```
A = [[1,0,0], [0,6,0], [0,0,5], [0,0,0]],    b = [11,1,1,1]
H = diag(1,36,25),                            g = [11,6,5]
x0 = [0,0,0]
x1 = [11231,6126,5105] / 31201
x2 = [87659,7599,16865] / 55219
x3 = [11,1/6,1/5]
```

`witness_full_column_rank` proves actual rank(A)=3. `witness_iterates` proves
unique exact Krylov minimization at k=0,1,2,3. Efficient membership representations:
x1=(1021/31201)g and x2=(16321g−383Hg)/110438. Orthogonality of each normal
residual against H applied to its entire Krylov space, together with H's
injectivity, certifies global unique minimization. Merely checking membership or
normal equations for a restricted finite candidate list is insufficient.

The exact residuals are
`r1=[331980,-5555,5676,31201]/31201` and
`r2=[519750,9625,-29106,55219]/55219`. Their normal squared norms are respectively
`3593700/31201` and `5336100/55219`, both positive. g is nonzero and x3 has zero
normal residual. Both compared iterates are nonzero and occur before exact
termination, which is at the third iterate. The residual norms' decrease is not
used as a surrogate for the backward-error comparison.

## First spectral upper certificate

Let κ=1979/2000 and w=[250,−1,1,27], with ω=wᵀw=63231. For x=x1, put
s=‖x‖₂², z=Ax, r=b−z, h=wᵀz,
`c0=r−w(wᵀr)/ω`, and `a0=−Aᵀw+(h/s)x`. The exact rational completion is

`E = −wwᵀA/ω + c0 xᵀ/s + h c0 a0ᵀ/(ω s κ−h²)`.

All divisions are real and every denominator needed by cancellation must be
proved nonzero. The proof establishes directly that E is feasible and that the
3×3 Gram matrix `κI−EᵀE` is positive definite. Its exact LDL factorization reduces
this to three positive rational diagonal coefficients and one fixed matrix
identity. The spectral norm bridge gives ‖E‖₂²≤κ, hence μ(x1)²≤κ. This replaces
the source's general spectral-completion lemma by direct verification of the
specific completion; it does not assume any completion theorem or scalar bound.

## Second spectral lower certificate and universal bridge

For x=x2, s=‖x‖₂², z=Ax, r=b−z, let C=AAᵀ,
`D=(‖r‖₂² I−rrᵀ+zzᵀ)/s`, and B=(5/6)C+(1/6)D. The exact identity is

`B−(99/100)I = K/2407881992100`,

```
K = [[206417059721, -50293465200, 1125984433750, -1435003762500],
     [-50293465200, 83658415217471, 206242965000, -26574143750],
     [1125984433750, 206242965000, 61800032332121, 80360210700],
     [-1435003762500, -26574143750, 80360210700, 11170189945871]]
```

K is real symmetric positive definite. Its four source leading determinants are
206417059721;
17265994657467102998545591;
960941324740480331793743845178086291011;
65442104145157248520714038046591467785805073713081.
A rational LDL identity with four positive pivots is an equivalent, usually
cheaper retained certificate. No numerical eigenvalue estimate is assumed.

`every_second_perturbation_large` must quantify over every feasible real 4×3 E.
If q=b−(A+E)x2 is nonzero, use u=q/‖q‖₂. Feasibility implies `(A+E)ᵀu=0` and
q=uuᵀb. The genuine induced spectral norm yields
`uᵀCu≤‖E‖₂²` and `uᵀDu=‖r−uuᵀb‖₂²/s≤‖E‖₂²`. Convex combination and positive
definiteness give 99/100<‖E‖₂². If q=0, Ex2=r and the same operator-norm bound
gives ‖E‖₂²≥‖r‖₂²/s>99/100 by exact rational arithmetic. This second case must
remain in the proof. It removes the need to formalize a general nullspace lemma
for every rectangular matrix without narrowing the witness's perturbation set.

Minimum attainment then gives
`μ(x1)^2 ≤ 1979/2000 < 99/100 < μ(x2)^2`.
Nonnegativity yields the strict comparison of the actual unsquared errors.

## Projection approximation and strict cutoffs

The projection-to-Gram theorem reduces the two values to a diagonal 3×3 inverse;
its three denominators are strictly positive. The exact squared values are

```
69694107852573439503892031925 / 69323394392991282508138323472
5430772101137459612205263871781350 / 5387955615790281743396033884265233
```

They satisfy `value1 < 503/500 < 1007/1000 < value2` (the source decimals 1.006
and 1.007 are exact rationals). Positivity converts this squared separation to
strict increase of the actual projected norms, on the same successive pair.

## Computation, LeanCert and trust plan

Use pinned Lean 4.33.1, Mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, and LeanCert
`621a43d7cf21f87872392a01e874f2f1dbddc926`. Structure follows the established
Schiffer/Forsythe statement/proof separation and repository examples IE-19/IE-23.
Set `leancert.trust` to `kernel` in proof files; use kernel-mode LeanCert for any
numerical obligation delegated to it and add `#assert_trust kernel` to every
export. Exact `norm_num`, ring identities, and positive rational LDL pivots avoid
interval arithmetic. **No interval boxes or numerical search are needed.** No
native_decide/native LeanCert, unverified eigenvalue oracle, imported custom axiom,
or proof-dependent definition is allowed.

The independent Challenge currently contains 17 intentional placeholders and is
never imported by Solution. Comparator lists all 17 public obligations, permits
only propext/Classical.choice/Quot.sound and no replaceable definitions. Actual
proof compilation, transitive axiom checking, default-kernel replay, real-sandbox
Comparator and negative controls must run on non-root Linux. No local heavy
build, new cached dependency tree, or local Lean invocation is authorized here.

Two independent statement referees must inspect the canonical norm and algorithm
semantics, full perturbation quantification, minimum attainment, Penrose bridge,
nontermination, strictness, and literal data. After proof completion, two
independent final referees must review actual proof source and actual Linux logs,
covering Tau Ceti scope/correctness/reuse/clarity angles. AI-agent review is not
human peer review or formal acceptance by Tau Ceti.

Before a complete individual upstream PR, add truthful formalization.yaml v0.4
metadata with George Stepaniants's Caltech CMS department and no email; retain
Colbrook's original mathematical credit and Cambridge DAMTP affiliation; include
proof-source correspondence, immutable evidence hashes and all reviews; render
and visually verify the affected problem PDF; and run permanent-ID/catalog
checks. No mathematical statement, problem ID, canonical path or historical
credit is to be changed.
