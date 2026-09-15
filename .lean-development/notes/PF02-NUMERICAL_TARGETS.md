# PF-02 — exact statements before proofs

Status: draft boundary only. No Lean typecheck, independent statement approval,
proof implementation or formal verification is claimed.

Formalization: George Stepaniants, Department of Computing and Mathematical
Sciences, California Institute of Technology, Pasadena, California, USA.
Mathematical counterexample: Matthew J. Colbrook, Department of Applied
Mathematics and Theoretical Physics, University of Cambridge.

## Original complete target

For every k >= 3, p,q >= 1, and every entrywise nonnegative REAL matrix M of
size p by q, assume its ordinary real rank is k(k+1)/2 and its real PSD rank
is exactly k. Its factorization fiber consists of ALL real PSD tuples
(A_1,...,A_p,B_1,...,B_q) with trace(A_i B_j)=M_ij. Each factor is k by k.
The fiber has the Euclidean subspace topology. The action is exactly
A_i -> S^T A_i S and B_j -> S^(-1) B_j S^(-T), for one common real invertible
S. Does the full orbit quotient, with the quotient topology, have to be connected?

`MinimalPSDOrbitConnectedConjecture` retains every quantifier and hypothesis.
`RealPSDRankEquals` states existence at k and minimality among EVERY positive
natural factor size. It is the source's minimum predicate, without using a
default value for a nonexistent minimum. Merely exhibiting size-three factors
will not prove this predicate.

`FactorizationSpace` is the subtype of the full finite product of all real
matrix entries satisfying the PSD and trace constraints. Mathlib's finite-product
and subtype topology is the prescribed Euclidean subspace topology. It is NOT
restricted to the two supplied tuples or to strictly positive definite factors.
`FactorizationOrbit` uses `Quot CongruenceRel`; the relation is precisely a common
invertible real congruence. Prove that it preserves the fiber and is already an
equivalence. Mathlib's `Quot` topology is coinduced by the quotient map; an explicit
export binds this actual instance, rather than substituting a discrete topology.

Connectedness is `IsConnected Set.univ`. The hypotheses imply the factorization
fiber is nonempty. A continuous separator of the entire quotient will refute
connectedness itself, not just path connectedness or uniqueness of factor tuples.

## Fixed exact counterexample

Use k=3 and p=q=6, so the required ordinary rank is 3*4/2=6. Preserve the source
matrix exactly:

```
24 20 20 16 16 16
20 24 20 16 16 16
20 20 24 16 16 16
16 16 16 14 12 12
16 16 16 12 14 12
16 16 16 12 12 14
```

The six source factors are 2I+2E_ii for i=1,2,3, followed by
2I+E_12+E_21, 2I+E_13+E_31, 2I+E_23+E_32. Both row and column factors use this
same list. In the second tuple, reflect ONLY the fourth factor, replacing its
(1,2) and (2,1) entries by -1, on BOTH sides of the factorization. Every factor
is real PSD; the source's stronger positive definiteness is available but not
needed to meet the canonical target.

The fixed coordinate convention on real symmetric 3 by 3 matrices is
(A_11,A_22,A_33,A_12,A_13,A_23), unnormalized. The trace metric in these coordinates
is diag(1,1,1,2,2,2). The exact obligations are:

- All 36 entries of M are strictly positive.
- Both complete sets of 36 trace products equal the same M.
- Their coordinate determinants are +32 and -32.
- det M = 8192 and ordinary rank M = 6.
- Real PSD rank M is exactly 3, including a proof that no size 1 or 2 factorization
  exists. Size zero is outside the source's minimum convention.

No approximate eigenvalue, tolerance, rational interval or floating-point input
is used in these statements.

## Entire-fiber and quotient obligations

For EVERY size-three factorization of this M, the row coordinate determinant is
nonzero. This follows from the actual trace-product identity
M = U_A diag(1,1,1,2,2,2) U_B^T and det M != 0.

For EVERY real 3 by 3 S, including singular S, prove the exact fixed-degree
polynomial identity det C_S = (det S)^4, where C_S is the coordinate matrix of
X -> S^T X S in the explicit symmetric basis. For invertible S the multiplier
is strictly positive even when det S is negative. Thus orientation sign survives
precisely all original real GL(3) congruences, rather than just orthogonal or
positive-determinant transformations.

Prove continuity of determinant sign on the whole fiber using nonvanishing.
Descend it along the actual quotient map. The resulting continuous function
on the entire quotient has range exactly {-1,1}, realized by the two genuine
factorizations. Its connected image would contain 0, which is impossible.
Therefore this actual quotient is disconnected, and the complete universal
canonical statement is false.

## Aggressive exact reduction and LeanCert

Prove only the explicit k=3 counterexample and its negation of the complete
universal target. The source's optional every-k constructions and nonquantitative
positive perturbation are not needed or advertised as formalized.

Avoid a new general dimension theorem for symmetric matrices. Minimality reduces
to r=1 and r=2; in size two, trace products factor through the three coordinates
(A_11,A_22,A_12), so ordinary rank is at most 3. Every r>=3 already meets the lower
bound. For nonvanishing at size three, use determinant multiplicativity on the
6-coordinate trace factorization directly.

Use exact small matrix identities, finite sums, determinants and positive Gram
certificates. Derive det M from the triangular/block coordinate matrix and the
diagonal trace metric, avoiding repeated expansion of all 6! permutations.
The sole generic congruence determinant identity has only nine scalar variables
and degree twelve; obtain a structured exact polynomial certificate on Linux.
No interval discretization over factors or changes of basis is permissible.

Keep pinned LeanCert with trust set to kernel, and check every exported theorem
using `#assert_trust kernel`. Pure algebraic work requires no artificial interval
subdivision. Actual LeanCert trust checks, fresh Linux compilation, default-kernel
replay, Comparator with no definition holes, the three permitted standard axioms
(or subsets), real sandbox and negative controls remain mandatory final gates.

## Frozen-boundary gate

Before implementation: Linux typecheck these definitions and all eleven
Challenge signatures; obtain two independent statement approvals; freeze their
actual bytes/hashes. No proof body exists in this draft. The draft author does
not count as an independent statement or final mathematical referee.
