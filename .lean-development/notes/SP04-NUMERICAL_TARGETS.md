# SP-04 — exact numerical statements before proofs

Status: complete statement draft only, with sixteen deliberate independent
Challenge placeholders. No proof implementation, actual typecheck, independent
approval, verification count or repository promotion is claimed.

Mathematics: Matthew J. Colbrook, Department of Applied Mathematics and
Theoretical Physics, University of Cambridge. Formalization: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. No email.

## Canonical target and required scope

The original rule concerns all real stationary pairs
  abs(det X)=1,  X^T(U-X)=cI,
and selects a pair with minimum abs(c). It claims that the selected X is a
nearest feasible matrix in Frobenius norm, for generic U in every dimension.
Both determinant signs are essential. "Generic" explicitly means outside some
proper real algebraic exceptional set. The source gives an open set of bad
3x3 inputs, not merely an exceptional rational diagonal example.

The final negation is expressed in dimension three: for every
nonzero real multivariate polynomial p in the nine entries, there is a real U
with p(U) nonzero, a uniquely least-absolute stationary pair (X,c), and a feasible
Y with strictly smaller Frobenius distance. This excludes every proper algebraic
exceptional set. The formal statement additionally requires a nonempty
Euclidean open set on which those witnesses exist. Frobenius squared-distance
inequalities are equivalent only after proving the ordinary nonnegative norm
bridge. A condition involving a single diagonal U would be an incomplete target.

Preserve the mathematical authorship of Matthew J. Colbrook, University of
Cambridge DAMTP. The formalization credit is George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology; no email. Do not copy the source manuscript's contact metadata into
new formalization files.

## Exact numerical obligations, before any proof bodies

For all real 7/4<s0<s1<s2<44/25:

1. With U=diag(s), every actual stationary X is diagonal. Its nonzero entries
   satisfy x_i^2-s_i*x_i+c=0 and abs(x0*x1*x2)=1. Derive this for every X, not
   only proposed diagonal candidates. If S=X^T*X, stationarity implies
   U^T*U=S+2cI+c^2*S^{-1}. Thus S commutes with diagonal U^T*U and is diagonal,
   since the squared s_i are distinct. Then X^T*U=S+cI directly kills every
   off-diagonal X entry, avoiding an unnecessary second inverse.
2. Exclude 0<=c<=13/25. The c=0 case forces x_i=s_i and product>1. For c>0,
   the roots are r_i=(s_i+sqrt(s_i^2-4c))/2 and c/r_i. Use two exact coarse
   parameter cases instead of differentiating r or subdividing finely:
   - 0<c<=2/5: 7/5<r_i<44/25. A product with exactly one small root is at most
     (2/5)*(44/25)^2/(7/5)=3872/4375<1.
   - 2/5<c<=13/25: 4/3<r_i<3/2. Such a product is at most
     (13/25)*(3/2)^2/(4/3)=351/400<1.
   Replacing further large roots by small roots decreases the product; all
   three large roots give product>1. Every root pattern is covered.
   The controlling quadratic tests are -9/100, -8/225 and 1/100, respectively.
   These strict rational margins make exact kernel algebra sufficient.
3. For t>=0 define a_i(t)=(s_i+sqrt(s_i^2+4t))/2 and
   b_i(t)=(sqrt(s_i^2+4t)-s_i)/2. Prove a_i*b_i=t, a_i-b_i=s_i,
   positivity of a_i, positivity of b_i for t>0, b_i<a_i, and strict increase
   of a_i,b_i in t. For fixed t, a0<a1<a2.
4. For g(t)=b0(t)*a1(t)*a2(t), prove continuity on [0,13/25], strict increase,
   g(0)=0, and g(13/25)>1. At the upper endpoint, a1,a2>2 and b0>1/4;
   these follow from 4-2s_i-13/25<0 and
   (1/4)^2+s0/4<1/16+(44/25)/4=201/400<13/25.
   The intermediate value theorem gives a unique t* in (0,13/25) with g(t*)=1.
5. The negative-multiplier roots are a_i and -b_i. Among all nonempty negative
   index patterns, the absolute product is uniquely largest for index set {0}:
   additional b_i/a_i factors are in (0,1), and t/a0^2 is the unique largest
   factor. For 0<t<t*, every such product is less than one; at t=t*, only
   (-b0,a1,a2) has absolute product one. No existence theorem for the later
   stationary roots is needed. The all-positive product is always>1.
6. Combine 1-5 to prove that X*=diag(-b0(t*),a1(t*),a2(t*)) and c*=-t* are
   the unique least-absolute stationary pair among ALL real stationary X,c.
   Flip the first sign to obtain Y with abs(det Y)=1 and squared-distance
   improvement exactly 4*s0*b0(t*)>0. This handles both determinant signs.

## Full genericity route using pinned foundations

Mathlib's inspected matrix APIs did not expose a complete SVD or continuity of
ordered singular values. Those are not needed for the full target. Build an
explicit local parameterization of an open family by rational rotations:

  u(t)=(1-t^2)/(1+t^2), v(t)=2t/(1+t^2),
  R_ij(t) has block [[u(t),v(t)],[-v(t),u(t)]] on coordinates i,j.

The denominators are positive for every real t. The equality u^2+v^2=1 proves
orthogonality by low-degree exact algebra. Let P(alpha) and Q(beta) each be the
product R01*R02*R12 and put
  F(s,alpha,beta)=P(alpha)*diag(s)*Q(beta)^T.
At alpha=beta=0 and s=(1751,1755,1759)/1000, the derivative consists of three
identity diagonal coordinates and one 2x2 block for each i<j:
  dU_ij=2*s_j*dalpha_ij-2*s_i*dbeta_ij,
  dU_ji=-2*s_i*dalpha_ij+2*s_j*dbeta_ij.
Its block determinant is 4*(s_j^2-s_i^2)>0. Give an explicit linear inverse to
these three blocks, instead of expanding a 9x9 determinant. The rational chart
is continuously differentiable; the pinned inverse-function theorem therefore
gives a nonempty open image after restricting s to its strict ordered box.

Orthogonal covariance carries the entire stationary-pair relation, absolute
determinant, uniqueness and Frobenius improvement from item 6 to every matrix
in that image. The stationary transform is Y=P^T*X*Q and its exact equation is
Y^T(diag(s)-Y)=Q^T*X^T(U-X)*Q. This is all finite matrix algebra; it does not
assume or require a generic SVD construction.

Finally prove that a nonzero real multivariate polynomial cannot vanish on a
nonempty open set. One direct finite-variable route is to restrict to each line
x0+t(y-x0), obtaining a univariate polynomial. The open set contains a nonempty
interval of parameters near t=0; infinitely many roots force that polynomial
to vanish identically. Evaluating at t=1 gives p(y)=0 for arbitrary y, and
MvPolynomial.funext forces p=0. Thus the counterexample open set meets the
complement of every proper algebraic exceptional set.

## Inspected API support and remaining work

- Matrix.NonsingularInverse, transpose/multiplication and determinant APIs cover
  the all-stationary diagonal reduction. PF-02 already exercises nearby APIs.
- Real.sqrt monotonicity, squared-root identities, exact rational arithmetic and
  interval intermediate-value theorems cover all numerical obligations. Only
  two c ranges are needed; no eigensolver, floating-point search or dense mesh.
- Analysis/Calculus/InverseFunctionTheorem/ContDiff.lean supplies
  ContDiffAt.toOpenPartialHomeomorph with an invertible continuous derivative,
  together with source/target neighborhood membership. FDeriv/Pi and Mul support
  entrywise derivatives; finite-dimensional linear equivalences are continuous.
- Polynomial.eq_zero_of_infinite_isRoot is present; MvPolynomial/Funext.lean
  supplies polynomial extensionality over infinite fields. A small line-
  restriction bridge must be proved explicitly.

The proof phase will need new ordinary matrix/calculus glue after independent statement
reviews. The statement draft does not assume an unproved substantive spectral, convex-geometric,
or external inequality theorem. It is larger than a single exact witness and
should be scheduled as a complete medium-size project. No partial diagonal-only
submission or weakened "generic" definition is recommended.

## Exact frozen-definition semantics and final bridge

All scalars and matrices are real. The canonical rule quantifies over every
natural n≥2. The counterexample uses n=3 and the complete strict interval
7/4<s0<s1<s2<44/25, with continuous real parameters. No rational-only data
restriction is permitted. Multiplier exclusion includes both c=0 and c=13/25;
the unique selected t satisfies 0<t<13/25. Negative-root facts include t=0 and
the entire half-line thereafter.

`frobeniusNorm` selects Mathlib's actual Frobenius norm instance explicitly,
not the default function-space sup norm. `frobenius_norm_squared` proves its
nonnegativity and equality of its square with the exact double sum of entry
squares. The strict final comparison concerns these unsquared actual norms.
`IsNearest` is the universal minimum predicate on every matrix with |det|=1,
without an empty-infimum default. `LeastAbsoluteMultiplier` quantifies over
EVERY actual stationary matrix and scalar. The uniqueness predicate proves
equality of both the matrix and multiplier for any tying competitor.

`GenericNearestRule` permits a separate arbitrary proper real algebraic set in
each dimension and restricts to unique choices, as the source explicitly
permits. Refuting this unique-choice rule is sufficient. `IsRealAlgebraicSet`
is the common zero locus of an arbitrary family of real polynomials in all
n² entries, even an infinite family. If this set is proper, a point outside
it identifies one member polynomial that is nonzero. Escaping that polynomial
zero locus escapes the entire common zero locus. Thus the final export covers
EVERY proper real algebraic exception, not only determinant/discriminant zeros.

`Counterexample U` includes an actual orthogonal decomposition with positive
distinct singular values in the strict source box, the actual unique least
stationary pair, and an explicit feasible improving matrix. These are proved
witnesses, not assumptions on arbitrary U. Generic finiteness of the stationary
set is source background rather than an added prerequisite for defining a
minimum: the source permits the unique-choice locus, and this proof constructs
and uniquely minimizes its actual selected pair directly. The open family
escapes every proposed algebraic exceptional locus.

Additional exact margins used above: at t=13/25,
  4−2(7/4)−13/25 = −1/50 < 0,
  (1/4)²+(44/25)/4−13/25 = −7/400 < 0.
The center values 1751/1000,1755/1000,1759/1000 lie strictly in order in the
source box. The three derivative block determinants, in order (01),(02),(12),
are 1753/31250,351/3125,1757/31250, all strictly positive. The derivative formula
is explicit in Definitions and its continuous linear inverse must be proved;
invertibility is not assumed in Challenge.

The sixteen advertised exports cover: actual Frobenius norm identity;
all-stationary diagonal reduction; full positive-root classification/bounds;
complete nonnegative-multiplier exclusion; negative-root identities and
continuity/monotonicity; unique normalization existence; all-pattern dominance
and equality case; unique diagonal counterexample and actual improvement;
full orthogonal covariance; rational rotation orthogonality; actual invertible
chart derivative; open chart image; full open counterexample family; arbitrary
nonzero-polynomial escape; arbitrary proper algebraic-set escape; and negation
of the complete all-dimensional generic rule.

## Mandatory approval and trust gates

No proof bodies before two independent source/statement reviews and an actual
successful Linux typecheck of Definitions and all sixteen Challenge signatures.
The reviewed bytes and hashes must then be frozen. The deliberate Challenge
placeholders may never enter Solution's import graph. Any later mathematical
boundary change reopens the two reviews. Use pinned LeanCert with explicit
kernel trust and assertions on every export, real fresh non-root Linux
Comparator/default-kernel/axiom/rejection controls, and at least two independent
final referees under the repository's pinned Tau Ceti adaptation. No local
Lean/Lake compilation, dependency download or cache restoration is permitted.
