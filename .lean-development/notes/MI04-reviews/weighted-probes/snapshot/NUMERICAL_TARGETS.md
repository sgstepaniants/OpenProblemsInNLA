# MI-04 exact mathematical and numerical obligations

Status: statement preparation only. There are no proof bodies, approvals, Lean runs or frozen declarations yet. The immutable original source is upstream `ce47b5630bf3680d9211131c3a43825b022c139a`, bound in SOURCE-PROVENANCE.json.

Original mathematical proof: Matthew J. Colbrook, Department of Applied Mathematics and Theoretical Physics, University of Cambridge. Formalization: George Stepaniants, Department of Computing and Mathematical Sciences, California Institute of Technology. These roles are separate; no personal formalization-author email is published.

## Complete original target

For every natural n with n >= 1 and every complex n-by-n matrix X, assume:

For every complex Hermitian A and B, if the actual 2n-by-2n matrix

    P = [ A   X  ; X*   B ]

is positive semidefinite, then its induced Euclidean operator norm is at most the induced Euclidean operator norm of A+B.

Prove that there exist a complex Hermitian K and complex scalars alpha,beta such that

    X = alpha K + beta I.

The universal A/B hypothesis is not replaced by a selected completion, positive definiteness, bounded entries, an invertibility condition or distinct singular/eigenvalues. Every matrix may be singular. All repeated values are retained. Alpha may be zero, including the scalar case. The final declaration spells out the original universal premise and affine-Hermitian conclusion explicitly.

Only the original necessity implication is proposed for formal verification. Colbrook's stronger four-way equivalence and converse are not advertised as established by this project. They are not required by the canonical question.

## Genuine norms, order, and extremal values

Every matrix norm is the norm of Matrix.toEuclideanCLM over complex EuclideanSpace. It is not a maximum-entry, Frobenius or default Pi matrix norm. Block indices are the disjoint sum of the two original index sets, with no coordinate omitted.

Matrix.PosSemidef and Matrix.IsHermitian are the actual Mathlib notions. Auxiliary topValue is the supremum of the real quadratic forms over all vectors of Euclidean norm exactly one. An explicit finite-dimensional attainment obligation proves that this supremum is an actual maximum. Further obligations establish positivity/order, positive-matrix norm and scalar-shift equivalences. No desired spectral fact is stipulated as part of a definition.

For each Hermitian T, set K_X(T)=[T X;X* -T]. The intermediate ExtremeSymmetry predicate is the literal equality topValue(K_X(T))=topValue(-K_X(T)), universally in T. The passage from the original hypothesis is a theorem obligation. In positive dimension, the opposite diagonal blocks imply both extrema are nonnegative. The positive completion b I+K, where b=topValue(-K), gives the first inequality; the sign-flip unitary diag(I,-I) and T -> -T give its reverse. The zero case is included.

Positive scaling and arbitrary unitary conjugation of X preserve this symmetry; both are proved, not assumed in the final theorem.

## Exact second-order calculation without analytic eigenvalue branches

The new formal proof arrangement replaces analytic simple-eigenvalue perturbation by two exact Rayleigh-quotient inequalities. This retains Colbrook's quadratic coefficient and avoids a new eigenvalue-analyticity development, growing computation or subdivision of a parameter interval.

Work with any finite nonempty complex coordinate space, real diagonal data d, distinguished coordinate a, and a Hermitian perturbation V. Assume exactly

    d_a = 1,
    d_j <= 1/2 for j != a,
    V_aa = 0.

No distinctness of the other diagonal values is assumed. Write g_j=1-d_j, so g_j >= 1/2 for j != a, and set

    w_a = 0,
    w_j = V_ja/g_j for j != a,
    L = sum_{j != a} |V_ja|^2/g_j,
    S = ||w||_2^2,
    R = Re(w* V w),
    M = ||V||_2.

For every real epsilon satisfying

    0 < epsilon,    epsilon (1+M) < 1/4,

prove the exact sandwich

    (L + epsilon R)/(1 + epsilon^2 S)
        <= [topValue(diag(d)+epsilon V)-1]/epsilon^2
        <= sum_{j != a} |V_ja|^2/(g_j-epsilon M).

All displayed denominators are proved positive: 1+epsilon^2 S >= 1 and g_j-epsilon M > 1/4. The lower bound evaluates the actual Rayleigh quotient of e_a+epsilon w and divides by its true squared norm. Its exact numerator is 1+epsilon^2(S+L)+epsilon^3 R. The upper bound decomposes an arbitrary unit vector into its a-coordinate and orthogonal remainder, bounds the latter perturbation quadratic form by M times its squared norm, and completes a weighted square in every remaining coordinate. Thus it holds for every vector, not just an eigenvector.

A separate theorem then squeezes the one-sided limit as epsilon tends to zero through positive values:

    [topValue(diag(d)+epsilon V)-1]/epsilon^2 -> L.

The condition epsilon(1+M)<1/4 is an auxiliary eventually-true neighborhood for each fixed V, not a restriction on X in the final target. No numerical eigenvalue evaluation, interval arithmetic, O-term axiom or convergence rate is assumed.

## Recovering every off-diagonal magnitude

For any distinguished i, use real diagonal D with d_i=1 and -1/2 <= d_j <= 1/2 for j != i. The only concrete probes needed are d_j=0 for all j != i, and the same probe with one chosen d_l=1/2. In both K and -K the unique top diagonal value is 1 and all other values are at most 1/2. The preceding limit and extreme symmetry give the exact weighted identity

    sum_j |X_ij|^2/(1+d_j) = sum_j |X_ji|^2/(1+d_j).

The diagonal terms have denominator 2 and cancel. Comparing the two probes changes precisely one off-diagonal weight from 1 to 2/3, a nonzero difference 1/3. Hence |X_il|^2=|X_li|^2. Unitary invariance and orthonormal-basis extension yield

    |u*Xv|=|v*Xu|

for every actual orthonormal pair u,v. Dimension one gives the correctly vacuous pair statement and is handled by the later algebraic conclusion.

## Normality, repeated values, and the affine line

Summing the pair equalities over a completed orthonormal basis gives ||X*u||=||Xu|| for every u. The actual matrix equality X*X=XX* is a theorem. The normal-matrix diagonalization obligation provides an actual unitary U and all n complex diagonal values z, with X=U diag(z) U*. It may be proved using the commuting Hermitian real/imaginary parts, Mathlib's orthogonal joint eigenspaces and a subordinate orthonormal basis; it is not assumed as an unproved imported normal spectral theorem.

For three distinct coordinates i,j,k one can replace the source's cube-root-of-unity vectors by the exact orthogonal pair

    u = (e_i+e_j+e_k)/sqrt(3),
    v = (e_i+I e_j-(1+I)e_k)/2.

Their unnormalized squared norms are exactly 3 and 4, and their inner product is zero. With a=z_i-z_k and b=z_j-z_k, the squared-modulus difference is

    |a+I b|^2 - |a-I b|^2 = 4 Im(a conjugate(b)).

Thus the pair condition forces every triangle orientation Im((z_i-z_k) conjugate(z_j-z_k)) to vanish. Repeated indices/values make the same conclusion zero directly. Only the exact identities sqrt(3)>0 and sqrt(3)^2=3 are needed; no transcendental root-of-unity calculation is required.

The affine-line obligation covers every finite list including coincident values: either all z are equal, or choose two distinct values and prove every value is beta+alpha t_j with real t_j. Conjugating the real diagonal t back by the actual unitary gives a Hermitian K. These steps include n=1, n=2, zero eigenvalues and arbitrary repetitions without artificial genericity assumptions.

## Proof and review boundary

The independent Challenge lists the complete generic variational, perturbation, geometric and final targets. After two independent statement reviews and actual successful non-root Linux elaboration, all proof dependencies will require kernel-checked implementation. LeanCert is to be used in kernel mode, including #assert_trust kernel for every export. No artificial interval certificate is needed for this symbolic route.

Only complete source-matched Comparator/default-kernel/axiom/control evidence and two independent final referees can support promotion. The statement package or an auxiliary perturbation lemma alone does not verify MI-04. No canonical status, problem ID, publication or verified count is changed here.
