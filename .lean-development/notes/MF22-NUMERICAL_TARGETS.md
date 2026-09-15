# MF-22: exact mathematical boundary before proofs

This is a statement draft. No proof, statement approval, Lean execution or
verified-count increment is claimed. The full canonical page and complete
manuscript are retained at upstream `8f04b905eb2e0827b6b84f37d9d080ae1f05b202`.

## Complete target and permitted simplification

For every fixed **real** parameter `rho > 0`, construct constants `K > 0`,
`alpha >= 0` and a natural `n0 >= 1` such that for every natural `n >= n0`,
the exact original complex block Toeplitz matrix is nonsingular and its
genuine spectral condition number is at most `K * n^alpha`.

The proposed formalization proves **alpha = 2**. The original question asks
for some polynomial exponent; its full target is therefore preserved. The
retained manuscript proves the stronger exponent 1, which this package does
not claim to certify. We simplify only the last norm estimate, bounding both
the matrix and its inverse by dimension times a uniform entry bound. There
is no restriction of the parameter domain, removal of `rho^2 = 10`, finite
size cutoff claimed uniformly in rho, modification of the Toeplitz boundary,
or replacement of the actual inverse by a surrogate.

## Field, indices, blocks and singularity

The ambient scalar field is `Complex`. A matrix of size `2n` is indexed by
`Fin n × Fin 2`; the first coordinate is the block index. For an integer
offset k, use these literal real coefficient blocks:

| k | B_k | C_k |
| --- | --- | --- |
| -1 | `(3/40) * [[-1,0],[-5,0]]` | `(1/80) * [[1,0],[7,0]]` |
| 0 | `(3/40) * [[0,-5],[16,-5]]` | `(1/80) * [[24,7],[0,25]]` |
| 1 | `(3/40) * [[-5,16],[-5,0]]` | `(1/80) * [[-25,0],[-7,-24]]` |
| 2 | `(3/40) * [[0,-5],[0,-1]]` | `(1/80) * [[0,-7],[0,-1]]` |

All other offsets give zero blocks. The entry at row `(j,a)` and column
`(k,b)` is `I*B_(j-k)(a,b) - rho*C_(j-k)(a,b)`, using integer subtraction.
Set `M_n = 80 H_n`. Both spectral norms use `Matrix.toEuclideanCLM` on the
actual complex Euclidean spaces. The condition number takes values in
`ENNReal`: it is infinity if the actual determinant is zero, and otherwise
`ENNReal.ofReal(norm(H_n)*norm(H_n^-1))`. Thus it cannot silently assign a
finite value to a singular matrix because Lean's nonsingular inverse is
totalized. The final theorem additionally exports eventual nonzero determinant.

## Exact recurrence and polynomial data

Write r=rho and define the six complex scalars
`A=-r-6I`, `B=-7r-30I`, `C=7r-30I`, `D=-25r-30I`,
`E=r-6I`, `F=25r-30I`. These names do not replace the coefficient blocks.
Set `a=30-r^2-10I*r` and `L=[[A,B],[B,D]]`, so `det L=24a != 0`.

The first two rows of T are
`L^-1 * [[24r,-96I,-F,-C],[-96I,-24r,-C,-E]]`.
Its final two rows are `[[1,0,0,0],[0,1,0,0]]`.
Let `G=[L^-1; 0]`, `e=(1,0,0,0)` and `E00=e e^T`.

For any genuine vector x, extend coordinates by zero outside `0,...,n-1`
using a finite sum over actual indices. For j>=0 define the state
`w_j=(u_j,v_(j-1),u_(j-1),v_(j-2))`.
The full equation `M_n x=f` is equivalent to the recurrence
`w_(j+1)=T*w_j+G*f_j` for every j<n. The automatically encoded boundaries
are `u_-1=v_-1=v_-2=0`, `u_n=0`; there is no condition on `v_n`.

Define polynomials over Complex by

```
N(z) = a + (-120-r^2+22I*r) z + 2(r^2+18) z^2
b = 24r^2+80I*r-240
c = 420-46r^2
d(z) = a + b z + c z^2 + conj(b) z^3 + conj(a) z^4
p(t) = a t^4 + b t^3 + c t^2 + conj(b)t + conj(a)
q(t) = a t^3 + (a+b)t^2 - (conj(a)+conj(b))t - conj(a)
```

The exported exact identities include `p=(X-1)q`, `q(1)=120I*r`,
`q(-1)=48(r^2-10)`, and for every complex z:

```
det(Id-zT) = d(z)/a
adjugate(Id-zT)_(0,0) = N(z)/a
T.charpoly = C(a^-1) * p
```

These are identities of the actual fixed matrix T. No formal generating
function, sampled values or source theorem is assumed to infer them.

## Root exclusion and the exceptional parameter

Prove `N(z)=0 -> d(z)!=0` for every complex z and every r>0. The exact
source elimination uses a quadratic resultant with real part
`2177280+946944r^2 > 0`. Its remaining putative root gives two real
quadratics at y=r^2,

```
R(y)=134136+32436y-10404y^2
J(y)=-103032-40632y+840y^2
70R(y)+867J(y)=-79939224-32957424y < 0.
```

The real cubic is `R_r(x)=6(r^2-10)x^3+25r*x^2+5(r^2-6)x+15r`.
Its discriminant is exactly
`-25r^4*(120r^4-3337r^2+34200)-5269500r^2-6480000`, which is negative.
The quadratic factor has leading coefficient 120 and discriminant -5280431,
so a completed square proves its strict positivity without intervals.

The denominator-cleared Cayley identity, for every complex x with
`1-I*x != 0`, is `(1-I*x)^3*q((1+I*x)/(1-I*x))=8I*R_r(x)`.
When r^2=10 the actual cubic degree drops to two. The resulting quadratic
has discriminant -14600; the missing Cayley root is t=-1, and
`q'(-1)=-100I*r != 0`. This case is part of the root-classification theorem.

The proposed root datum is an injective function `roots : Fin 4 -> Complex`
whose values are all nonzero zeros of p, with `roots 0=1`,
`norm(roots 1)=1`, `norm(roots 2)<1`, and `1<norm(roots 3)`.
Its **existence** for every r>0 must be proved. No final result may assume
this datum without exporting and using that existence theorem.

## Spectral projectors, bounds and the actual inverse

For each root define its spectral projector by evaluating the degree-three
Lagrange basis polynomial at the actual T. Export the full identities:
sum of projectors = Id; their pairwise products are the same projector on
the diagonal and zero otherwise; and `T^j=sum_i roots_i^j * Pi_i` for every
natural j. For `lambda=roots 3`, `Pi=Pi_3`, `gamma=Pi_(0,0)`, prove
`gamma!=0` and `Pi*E00*Pi=gamma*Pi`. The latter is essential: idempotence
alone would not justify the cancellation in the Green kernel.

Let `R_j=T^j-lambda^j*Pi`, `a_n=(T^n)_(0,0)` and
`d_n=a_n/(gamma*lambda^n)`. The proposed bound exports constants C,D>0
and n0>=1 so that for every natural j, `norm(R_j)<=C`, and for every
n>=n0, `a_n!=0`, `1/2<=norm(d_n)` and
`norm(1-d_n^-1)<=D*(norm(lambda)^n)^-1`.

For 0<=j<=n and 0<=ell<n, define the actual four-by-two Green matrix

```
K(j,ell) = (if ell<j then T^(j-1-ell)*G else 0)
           - a_n^-1 * (T^j*E00*T^(n-1-ell)*G).
```

The first natural subtraction is used only in the guarded branch; the
second is nonnegative on the stated domain. Recover inverse entries for
row `(j,0)` from row 0 of `K(j,ell)`, and for row `(j,1)` from row 1 of
`K(j+1,ell)`. The resulting genuine square matrix Q must satisfy
`M_n*Q=Id` and equal `M_n^-1` whenever n>=1 and `a_n!=0`.

The growing terms cancel by `Pi*E00*Pi=gamma*Pi`. Prove a single bound B>0
on every entry of K for all n>=n0, all j<=n and all ell<n. Recovering all
u/v coordinates gives the same bound on every entry of Q. Conversion back
to H multiplies inverse entries by 80; this factor must be retained.

Finally obtain E>0 bounding every entry of H_n, independently of n, and
B'>0 bounding every entry of H_n^-1 for all n>=n0. The genuine complex
operator norm satisfies `norm(A)<=dimension*entryBound`. Thus
`norm(H_n)*norm(H_n^-1)<=4*E*B'*n^2`. Choose positive K accordingly.

## Trust, optimizations and credit

All nontrivial finite checks are exact integer/rational/complex polynomial
identities. There is no interval subdivision, numerical eigenvalue solver,
root isolation or n-dependent determinant expansion. Constants depending on
rho may be chosen existentially; the full quantifiers must remain explicit.
LeanCert kernel assertions and the standard three-axiom audit are required
for every eventual exported theorem. The independent Challenge and actual
Comparator run must check the complete final statement and all advertised
bridges without replaceable definition holes.

Original manuscript and formalization author: George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. The original family and source root
classification remain credited to Bogoya, Böttcher, Ferrari, Grudsky and
Serra-Capizzano. No email is to be included. AI assistance and automated-agent
review must be disclosed accurately; neither constitutes human peer review.
