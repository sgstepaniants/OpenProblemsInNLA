# RA-02 source correspondence

This is an unapproved statement draft. The complete canonical target is
`randomized-and-low-rank-approximation/RA-02/README.md` at upstream
`ce47b5630bf3680d9211131c3a43825b022c139a`. Its ID, path, original mathematical
question and canonical status are not edited by this private draft. Original
mathematical credit remains Matthew J. Colbrook, University of Cambridge,
Department of Applied Mathematics and Theoretical Physics. George Stepaniants,
Caltech Department of Computing and Mathematical Sciences, is credited for
this AI-assisted formalization draft and integration, not for replacing that
mathematical authorship.

The full 637-line manuscript was read during the preceding mathematical
preflight. Its exact raw source digest is retained in SOURCE-PROVENANCE.json.
The local manuscript copy here removes only its contact address, is explicitly
labelled contact-redacted, and has its own different hash. All mathematical
content and attribution remain. It must not be described as the raw Git blob.

## Original objects and quantifiers

| Original mathematical object | Exact definition and mandatory bridge |
|---|---|
| Complex Hermitian PSD n-by-n A, n>=1 | `Square n` is `Matrix (Fin n) (Fin n) ℂ`; use Mathlib `Matrix.PosSemidef`, including Hermitian symmetry, with explicit `1<=n`. No real-only or invertible restriction is imposed on the universal target. |
| Pivot diagonal/trace mass at nonzero residual | `pivotMass` uses actual real diagonal and real trace. `pivot_kernel` proves real trace is positive for every nonzero PSD matrix, so the totalized branch agrees with the original ratio. Imaginary parts vanish by Hermitian/PSD semantics. |
| Rank-one Cholesky update | `choleskyStep` uses complex entries and exact division. At a zero diagonal it returns the residual; `pivot_kernel` proves such events have mass zero at nonzero PSD residuals. PSD preservation is a conclusion to prove. |
| Zero-residual convention | The zero-trace branch uses uniform dummy labels of mass 1/n. Trace zero iff the PSD residual is zero; `zero_residual` proves every later residual and expected trace are zero. Random dummy labels cannot change the residual law. |
| Adaptive path probability | `pathWeight` multiplies successive conditional masses using the actual chronological `pathResidual`. `finite_path_law` proves nonnegativity, normalization over all paths, and extension identities. Successive labels are not assumed independent. |
| E trace(R_r), exactly r steps | `expectedTrace A r` sums over the full finite space `(Fin r -> Fin n)`. Repeated and zero-probability paths remain in that space. `expected_trace_recursion` supplies the conditional-expectation recursion. No extra steps or restricted sample space is used. |
| Decreasing actual real eigenvalues | `orderedEigenvalues` uses Mathlib `IsHermitian.eigenvalues₀` and an explicit `Fin.cast` by card(Fin n)=n. `ordered_spectrum` includes actual nonzero eigenvectors, antitone order and trace sum. |
| tau_r=sum_(j>r) lambda_j | `rankTail` sums the sorted list at zero-based indices i>=r. `spectral_tail_semantics` proves nonnegativity, rank-n empty tail and the exact single last eigenvalue at order r+1. The separate Rayleigh contract refers to the actual conjugate quadratic form and squared Euclidean norm. |
| Absolute C>0 and p>=0, independent of n,r,A | `PolynomialTraceFactor` has outer real C,p and inner full n,A,r quantifiers, with 1<=r<=n. `universal_counterexamples` gives strict violations for every real C,p and `no_polynomial_trace_factor` negates this entire proposition. |

## Proof route and exported obligations

The manuscript proves a stronger sharp limiting ratio 2^r, including
entrywise-positive examples. This draft instead uses the independently
reviewed finite arrowhead route in `sources/route/FINITE-ROUTE.md` and seeks the
weaker lower factor 2^r/3 for every rank. That factor still disproves the
**full original** polynomial-factor assertion. It neither claims the source's
stronger limiting theorem nor asserts that this finite construction is its
construction. Real-entry positive-definite witnesses are a valid subset for
negating a universal assertion over complex PSD matrices.

| Challenge declarations, all prefixed NLA.RA02 | Mathematical obligation |
|---|---|
| `exp_one_bound`, `scalar_parameters` | Sole kernel-mode LeanCert point certificate and exact symbolic rank-dependent parameters. |
| `pivot_kernel`, `finite_path_law`, `zero_residual`, `expected_trace_recursion` | Genuine normalized PSD process, including zero events, all histories and actual expectation. |
| `ordered_spectrum`, `least_eigenvalue_rayleigh`, `spectral_tail_semantics` | Genuine spectral semantics, not a proxy eigenvalue/tail definition. |
| `arrowhead_quadratic`, `arrowhead_positive_definite`, `rayleigh_probe_values`, `arrowhead_tail` | Exact family, nonvacuous complex PD witnesses, exact probe, positive actual tail bounded by epsilon^r. |
| `residual_state_positivity`, `residual_state_updates`, `distinct_history_state`, `distinct_history_identity` | Both closed residual states agree with actual Cholesky updates; every distinct r-step path satisfies exact pivot/trace cancellation and the probability-weighted contribution identity. |
| `retained_history_count`, `retained_prefix_description` | Carried-label binary encoding is injective, has cardinality 2^r, never repeats labels and gives the exact prefix selected sets. |
| `retained_trace_bound`, `retained_contribution_bound`, `expectation_lower_bound` | All retained prefixes, every rank including one, direct identical-product cancellation, and a lower bound on the full normalized expectation. |
| `binomial_exponential_bound`, `exponential_tail_factor` | Existing symbolic binomial-to-exp inequality consumes exp(1)<=3 to bound the actual tail ratio. |
| `exponential_dominates_real_power`, `universal_counterexamples`, `no_polynomial_trace_factor` | Arbitrary real p, strict violations, positive actual tails, complete original universal negation. |

The contract count is 27. Internal helper declarations may later split these
arguments, but their hypotheses and conclusions must stay fixed after the
approved statement freeze. `Challenge.lean` has only deliberate placeholder
bodies, while every definition is concrete and unsorried. The future proof
must not import Challenge. No conclusion is stored as an assumption in a new
structure or assigned by a definition.

Boundary checks include n=1, r=1, r=n, zero and singular PSD inputs, zero
probability choices, repeated labels, empty paths/sums, complex inputs and
vectors, the complete final constants quantifiers, and positive actual tails.
The explicit family is used only with r>=1; total definitions at r=0 make
auxiliary expressions well-formed without extending the original target.

Existing public work was checked in the fresh bounded audit described by
DUPLICATE-AUDIT.json: 14 repositories, 251 public heads, 205 complete trees and
152 PR records at 2026-09-16 08:38 UTC. No target-named RA-02/RPCholesky Lean or
formalization.yaml was found. The mathematical PR 106, distinct RA-03 Lean
PR 157 and partial RA-01 PR 237 were read and distinguished. This is not a
claim about private, unpushed, later or unusually named work.
