# RA-02: exact statements before proof implementation

**Statement draft only.** This document is authored and hashed before either
new Lean statement file. No proof implementation, Lean elaboration, LeanCert
execution, Comparator run, independent statement approval, or verification
count is claimed. The final boundary is the complete negative answer to the
canonical RA-02 question at upstream commit
`ce47b5630bf3680d9211131c3a43825b022c139a`.

Original mathematical resolution: Matthew J. Colbrook, Department of Applied
Mathematics and Theoretical Physics, University of Cambridge. Formalization
draft and integration: George Stepaniants, Department of Computing and
Mathematical Sciences, California Institute of Technology. AI assistance is
disclosed. The finite arrowhead route below is a proposed alternative proof of
the same negative target, reviewed mathematically before this statement draft;
it is not asserted to be the manuscript's construction or a historically new
result. The manuscript's sharp limiting factor, entrywise-positive examples,
LU results and correlation-matrix extensions are outside this target.

## 1. Full target and exact finite probability semantics

For every natural dimension n>=1, A is an arbitrary complex n-by-n Hermitian
positive-semidefinite matrix, expressed by Mathlib's actual Matrix.PosSemidef.
The target rank is every natural r with 1<=r<=n. Both constants C>0 and p>=0
are arbitrary real numbers, independent of n,r,A. The positive assertion to
negate is

    exists real C>0, exists real p>=0,
      forall n>=1, forall complex PSD A of order n, forall 1<=r<=n,
        E[trace(R_r)] <= C * Real.rpow(r,p) * tau_r(A).

Exactly r steps are taken. Finite paths include every ordered label sequence,
including repeated labels and zero-probability events; they are not restricted
to the selected counterexample paths.

Write trR = Re(trace R). Define the total update at label j by leaving R
unchanged if R_jj=0, and otherwise by the actual complex rank-one formula

    next(R,j)_ab = R_ab - R_aj * R_jb / R_jj.

For PSD R, a zero-diagonal event has zero probability unless the whole residual
is zero. Define the label mass as Re(R_jj)/trR when trR is nonzero. When trR=0,
use the harmless uniform dummy-label mass 1/n. For PSD matrices this branch is
exactly R=0 and every following residual stays zero. This convention normalizes
the finite path law without changing any residual random variable.

For a list w of labels, define residual and path weight recursively in its
chronological order. The empty residual is A and the empty weight is 1. A
nonempty path j::w first applies next(A,j); its weight is the conditional mass
at j times the weight of w starting at next(A,j). The actual expected trace at
step k is the finite sum over all functions Fin k -> Fin n of path weight
times terminal real trace, after converting the function to its ordered list.
No independence of successive pivots is assumed.

Mandatory semantic obligations are nonnegative normalized one-step masses,
positive real trace for nonzero PSD residuals, equivalence of trace zero and
zero residual, PSD preservation for every total update, zero mass on an active
zero diagonal, normalized nonnegative full path weights, chronological
extension identities, zero-residual absorption, and the usual expectation
recursion. These are theorems to prove, not fields or assumptions in a custom
random-process structure. Normalized finite weights suffice to define a
finite probability distribution and its expectation; no measure-theoretic
surrogate or sum restricted to retained paths is substituted.

## 2. Genuine ordered spectral tail

For Hermitian A, use Mathlib's actual real eigenvalues `eigenvalues₀`, in its
proved decreasing Fin order, transporting only the equality card(Fin n)=n.
Do not assume the separately reindexed `eigenvalues` is sorted. Define

    tau_r(A) = sum over i:Fin n with r<=i.val of lambda_i(A).

The zero-based condition r<=i.val is the original one-based condition j>r.
Prove decreasing order, actual nonzero eigenvectors, and trace equal to the
sum of these eigenvalues. Prove nonnegativity for PSD A and the empty tail at
r=n. At order r+1 prove the rank-r tail equals the last eigenvalue. Also prove
the genuine least-eigenvalue Rayleigh bound for every nonzero complex vector.
The construction's epsilon^r is only an upper bound on this actual tail, never
the definition of the tail.

## 3. Explicit exact family, states and probe

For every integer r>=1 set, in exact real arithmetic,

    t=1/(2r+1), epsilon=t^(2(r+1)), d_i=epsilon^i, alpha_i=t^(i+1).

There are r ordinary labels i:Fin r and the distinguished label r in Fin(r+1).
The complex matrix has real entries

    A_ij = d_i when i=j<r, and 0 when i!=j<r;
    A_ir = A_ri = d_i alpha_i;
    A_rr = epsilon^r + sum_(i<r) d_i alpha_i^2.

Define it as the full unselected instance of the explicit residual state below.
Prove 0<t<1, 0<epsilon<=t^2<1, and all d_i,alpha_i are positive. Prove the exact
complex quadratic identity

    Re(x* A x) = sum_(i<r) d_i |x_i+alpha_i*x_r|^2 + epsilon^r |x_r|^2,

and actual Matrix.PosDef, not merely positive diagonals. For q_i=-alpha_i,
q_r=1, prove q!=0, Re(q*A*q)=epsilon^r and squared Euclidean norm
1+sum alpha_i^2>=1. Deduce 0<tau_r(A)<=epsilon^r through the genuine spectral
Rayleigh theorem. All statements are symbolic in r; no numerical eigensolve
or explicit large rational matrix is allowed to replace them.

For U a finite set of unselected ordinary labels, let

    c(U)=epsilon^r+sum_(i in U) d_i alpha_i^2 > 0.

If the distinguished label remains, the zero-padded state is the same
arrowhead on U and that label, with distinguished diagonal c(U). If it was
selected, the zero-padded active ordinary block is

    diag(d)_ij - (d_i alpha_i)(d_j alpha_j)/c(U),  i,j in U,

and the distinguished row/column is zero. Selected ordinary rows/columns are
zero in both cases. Prove these states are PSD; their active ordinary pivots
are respectively d_i and d_i*c(U\{i})/c(U)>0. Ordinary pivot i removes i from
U, and the distinguished pivot changes the first state to the second. These
identities must follow from the actual total rank-one update.

Every distinct history of length at most r+1 has exactly the state defined by
its unselected ordinary labels and whether the distinguished label is absent
from the history. For every distinct history w of length exactly r, define
prefix trace product and pivot product from its actual chronological residuals.
Prove both exact identities

    product(pivots) * terminal trace = D,
    pathWeight(w) * terminal trace = D / product(prefix traces),
    D = epsilon^r * product_(i<r) d_i.

No probability approximation, determinant surrogate, or asymptotic parameter
limit is used in these identities.

## 4. Binary histories and all prefix bounds

For a bit vector b:Fin r -> Bool, start with carried label c_0=r. At position
u<r the two choices are u and c_u. If the bit is false, select u and keep the
carry. If it is true, select c_u and replace the carry by u. The carry function
is total beyond r by leaving it fixed, but only positions <=r enter contracts.
The retained history is the resulting function Fin r -> Fin(r+1).

Prove that the encoding is injective, gives exactly 2^r distinct full paths,
and every such path has distinct labels. At each s<=r its selected prefix set
is exactly ({labels below s} union {r})\{c_s}; also c_s=r or c_s.val<s. These
contracts establish both state patterns, including s=0 and the terminal s=r.
No binary or factorial path enumeration is part of the universal proof.

For every r>=1, every bit vector and every prefix s<r, prove the actual trace
T_s obeys

    0 < T_s <= epsilon^s * (1+1/r).

The exact elementary route bounds T_s/epsilon^s by 1+(2r+1)t^2, then uses
(2r+1)t^2=1/(2r+1)<=1/r. The last-unselected case has a geometric ordinary
sum, weighted alpha sum and epsilon remainder. In the last-selected case
cancel the single missing ordinary diagonal before bounding; the remaining
scaled exceptional term has exponent
2(r+1)(r-s)-2(j+1)>=4, hence is <=t^2. Handle selected zero rows, the empty
geometric remainder at s=r-1, and rank one explicitly. There is no second
state case at s=0; r=1 has only this prefix.

Use direct cancellation of the identical products product_(i<r)d_i and
product_(s<r)epsilon^s. Do not expand the triangular exponent or compute tiny
rationals. Each retained path then contributes at least

    epsilon^r/(1+1/r)^r.

Normalized full path weights and nonnegative omitted contributions give

    E[trace(R_r)] >= 2^r*epsilon^r/(1+1/r)^r.

## 5. Sole fixed numerical certificate and complete contradiction

The only planned LeanCert obligation is the exact point bound

    Real.exp 1 <= 3.

Use kernel trust mode, the lowest adequate Taylor order/precision and no
interval subdivision. This certificate must be genuinely consumed. The
symbolic existing exponential inequality gives (1+1/r)^r<=exp(1); combine
these to prove for every r>=1

    E[trace(R_r)] >= (2^r/3) * tau_r(A).

For all real C>0 and real p>=0 prove existence of a natural r>=1 with
3*C*Real.rpow(r,p)<2^r using exponential-versus-real-power asymptotics. The
positive actual tail then yields a strict counterexample to the original
bound. Export both arbitrary-C,p counterexamples with an actual complex
positive-definite witness and the full negation of the original universal
complex-PSD assertion. An integer-only exponent, fixed rank, bounded dimension,
helper ratio alone, or positive-tail assumption instead of its proof would be
insufficient.

## Planned independent Challenge boundary

The 27 contracts cover, in this order: exp(1); parameters; one-step PSD kernel;
full finite path law; zero absorption; expectation recursion/nonnegativity;
ordered spectrum; Rayleigh minimum; tail semantics; quadratic identity;
positive definiteness; explicit probe; actual positive tail; residual-state
positivity; exact state updates; every distinct-history state; pivot/history
identity; binary injectivity/cardinality/distinctness; carry/prefix description;
all prefix trace bounds; retained contribution; full expectation lower bound;
symbolic binomial bound; actual-tail factor; arbitrary-real power domination;
full counterexamples; and canonical nonexistence. Definitions contain no
unproved semantic facts or fields encoding any of these conclusions.

Two nonauthor statement referees must approve the exact final hashes and the
actual Linux elaboration must pass before an immutable statement freeze can
authorize implementation. The draft's author cannot serve as either of those
statement referees. Later complete-source reviews, full default-kernel and
axiom audits, real Linux Comparator with rejection/sandbox controls, and exact
publication-commit reruns remain mandatory. This file records intended
statements and computation strategy, not completed verification.
