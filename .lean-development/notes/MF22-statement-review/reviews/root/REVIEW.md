# MF-22 independent mathematical statement review

**Approve the complete mathematical boundary for remote elaboration and the
second independent review.** This is not proof or mechanical acceptance.
Reviewer /root contributed no MF-22 definition, Challenge or proof code.
Both independent approvals and an actual elaboration receipt must precede
an immutable freeze and implementation.

I read the complete canonical original problem and full solution manuscript,
every definition and all 22 Challenge declarations, numerical obligations and
source correspondence. The original source files are unchanged from the cited
8f04b905 revision to observed upstream ce47b563. All eight real coefficient
blocks, offsets -1 through 2, integer row-minus-column convention, complex
field and uncorrected finite Toeplitz truncation are retained literally.
The parameter is every fixed positive real number; constants and cutoff may
depend on it, but never on the running size. Product indexing has dimension
2n. The norm is the induced complex Euclidean operator norm. Singular matrices
explicitly have infinite ENNReal condition number, and the final target also
proves eventual nonzero determinant, avoiding totalized-inverse vacuity.

Exponent two is sufficient for the original existential polynomial-growth
question, which specifies no exponent. It is obtained only at the final norm
conversion by bounding both norms from their entry bounds. This accepts the
whole original target and does not certify the manuscript's sharper linear
bound. Publication metadata must preserve that distinction.

The transfer data use the actual inverse of the proved invertible 2x2 leading
block. The state coordinates, zero extension, all right-hand sides and source
recurrence equivalence recover exactly three left zeros and u_n=0; v_n is not
used or constrained by an extra equation. The Green reconstruction includes
state n, so the final v_(n-1) entry is retained. The right and left inverse
identities and actual nonsingular inverse equality are proof obligations.
The inverse of H is 80 times the inverse candidate for M=80H; the scaling is
explicitly retained.

I checked the polynomial and root-classification obligations against the full
source: actual determinant/cofactor/characteristic identities, no numerator
cancellation, Cayley identity over complex arguments, discriminant negativity,
and the degree-drop rho^2=10 case with simple missing Cayley root -1. Four
distinct nonzero roots are proved to exist; no final theorem assumes RootData.
Actual Lagrange polynomials evaluated at T define the projectors. Their sum,
orthogonality and every power are proved, as are nonzero gamma and the stronger
Pi E00 Pi = gamma Pi identity needed for cancellation. Idempotence alone is
not substituted for that identity.

The remainder and normalized-boundary estimates use fixed constants and an
eventual cutoff. The Green bounds quantify over every n beyond it, every
j<=n and every ell<n. The potentially negative first exponent is guarded by
ell<j; the other natural exponent is valid under ell<n. In both cases j>ell
and j<=ell, cancellation leaves only bounded powers or a growing factor
multiplied by the proved exponentially small normalized-boundary error.
Every inverse entry is recovered. Consequently a dimension-factor norm bound
gives a polynomial estimate for the genuine condition number, for every fixed
positive parameter. Neither finitely sampled parameters nor matrix sizes,
interval subdivision or a synthetic inverse can settle this target.

The proposed exact fixed-size algebra and symbolic spectral/recurrence work
are appropriate optimizations. LeanCert kernel trust, real isolated Comparator,
default-kernel replay, standard transitive axioms, negative controls and two
final independent mathematical/runtime referees remain necessary later gates.
No local Lean/Lake/cache operation or proof acceptance is claimed here.

George Stepaniants is credited with the Caltech Department of Computing and
Mathematical Sciences affiliation and no personal email. Original family,
question and source classification credit remains with Bogoya, Böttcher,
Ferrari, Grudsky and Serra-Capizzano. This is an independent AI-agent review
under the scoped Tau Ceti protocol, not external human peer review.
