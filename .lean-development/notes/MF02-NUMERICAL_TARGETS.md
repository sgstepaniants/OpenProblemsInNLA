# MF-02: proposed numerical and semantic boundary

This is a proof-free draft, not a verified result. No local Lean/Lake process has
been run. Two independent statement approvals and a Linux type check are required
before freezing these bytes and implementing proofs. The canonical status stays
`Solved` until full proof, Comparator, kernel, referee and publication gates pass.

## Immutable source and authorship

Repository: `ajt60gaibb/OpenProblemsInNLA`, commit
`8f04b905eb2e0827b6b84f37d9d080ae1f05b202`.

- `matrix-functions-and-stability/MF-02/README.md`, SHA-256
  `b779c356388860ddeab25dc9b6f35d968b6f42625c598038fa402e6841b477c9`.
- `matrix-functions-and-stability/MF-02/solution.md`, SHA-256
  `e104a785ddecbec117f6dffe58110222550dd7f1354bfda8c67c37daa68c1924`.
- The entire proof note, Sections 1–6, was inspected; the target is its full
  uniform asymptotic theorem, not just its cubic coefficient inequality.

Formalization author and expository proof-note author: **George Stepaniants**,
Department of Computing and Mathematical Sciences, California Institute of
Technology, Pasadena, California, USA. No contact email is included. Prior
mathematical credit remains with Chen and Chow for the optimized cubic and Cheon,
Kim and Kim for prior constant-factor complexity results. The source workshop
problem remains credited to its authors. No novelty claim is made.

## Full canonical target

The parameter `m` is any natural number, including zero. The gap `δ` is any real
number with `0 < δ < 1`. There are no hidden rationality, fixed-gap or quantitative
separation-from-endpoint assumptions. The same constants apply when δ depends
arbitrarily on m. Inputs are the two **closed** intervals

`Iδ = [-1,-δ] ∪ [δ,1]`.

All polynomials and coefficients are real. The target function is ordinary real
sign, equal to -1 and 1 on the respective intervals. There is no matrix norm or
probability law in this scalar polynomial identity model. The same polynomial
must represent an arithmetic algorithm valid for matrices of arbitrary size;
there is no fixed-matrix minimal-polynomial reduction.

Starting from the actual polynomials 1 and X, a program can form arbitrary real
linear combinations freely and use at most m nonscalar multiplication gates.
Stored outputs may be reused. `ProductHistory` records all product gates and
retains every old register; `freeSpan` contains exactly all finite real linear
combinations of those registers. Multiplication operands and final output must
belong to that span. This encodes sharing, rather than a formula-tree cost that
charges again for reuse. Free intermediate linear combinations can be inlined
into the next operands without changing the gate count. A product with a scalar
operand is already a free scalar multiple, so counting a redundant such gate
cannot add outputs to the at-most-budget class. No division, comparisons,
piecewise polynomial selection, or access to the variable as a coefficient is
permitted.

`uniformError δ p` is the real supremum of `|p(x)-sign(x)|` on Iδ. Its Challenge
contract includes that the image is bounded and its supremum is attained (in the
equivalent displayed maximum/upper-bound formulation). Thus a default supremum
for an empty or unbounded set cannot discharge the theorem.

`unrestrictedError m δ` is the real infimum over the full program class, and
`cubicError T δ` is the real infimum over exactly T permitted stages. Every stage
has the form `a*x+b*x^3`, with arbitrary real coefficients. A zero coefficient or
degenerate stage is allowed. The empty composition is X. A successor composes its
new cubic on the outside. The function class is not restricted to the optimized
construction. All error classes are nonempty and bounded below by zero; proofs
must establish the real-infimum hypotheses each time they are used. No optimizer
for either coefficient infimum is assumed or advertised.

`stageMinimum m δ` is the infimum of natural T with `C_T ≤ E_m`, taken in
`WithTop ℕ`. This gives `inf ∅ = ∞` exactly as on the canonical page. The proof
must establish that a finite minimum exists before extracting a natural value.

The complete result is:

1. `T_min(0,δ) = T_min(1,δ) = 1`.
2. For every m ≥ 2, `floor(m/2) ≤ T_min(m,δ) ≤ m`.
3. For every m ≥ 0, there is a natural T equal to the extended-natural minimum
   and `(m+1)/4 ≤ T ≤ m+1` as real inequalities. This proves the full canonical
   uniform `Θ(m+1)` order with explicit absolute constants 1/4 and 1.

Exact optimal stage counts, leading constants, and the stronger same-budget
error-optimization question are not claims of either the retained note or this
formalization. These omissions do not weaken the literal canonical asymptotic
target, but must remain visible in final metadata and source correspondence.

## Numerical and analytic obligations

Set `r(a)=(1-a)/(1+a)`. For every `0 < a < 1`, prove `0 < r(a) < 1`.

1. Every program using m product gates has degree at most `2^m`, even with
   arbitrary free linear combinations and shared stored values. A length-T cubic
   composition has degree at most `3^T` and belongs to the program class with
   budget `2*T`. Neither inequality may be built into an assumed theorem field.
2. For every D ≥ 1 and every real polynomial p of degree at most D,
   `r(δ)^D ≤ uniformError δ p`. This includes zero polynomials and non-odd p.
   Symmetrizing to the odd part must be justified on both complete intervals.
   If e < 1 is its error, write its square as B(x²), with degree(B) ≤ D and
   B(0)=0. Apply the exterior Chebyshev bound after mapping [δ²,1] to [-1,1].
   The cases e ≥ 1 and e = 0 require explicit treatment.
3. The cubic construction uses
   `A=1+a+a²`, `M=2*A*sqrt(A)/(3*sqrt(3))`,
   `g_a(x)=x*(A-x²)/M`, and `φ(a)=a*(1+a)/M`.
   This writes `A^(3/2)` exactly as `A*sqrt(A)` and avoids real-power automation.
   Prove M > 0, `0 < φ(a) < 1`, and `φ(a) ≤ g_a(x) ≤ 1` for **every** x ∈ [a,1].
4. Prove `φ(a) ≥ 2*a/(1+a²)` by positive-denominator elimination and squaring;
   the exact residual is

   `27*(1+a)^2*(1+a^2)^2 - 16*(1+a+a^2)^3`

   `= (1-a)^2*(11*a^4+28*a^3+30*a^2+28*a+11)`.

   Consequently `r(φ(a)) ≤ r(a)^2`. The quartic factor is strictly positive
   throughout [0,1]. The assumptions needed before squaring must be proved.
5. For T ≥ 1, iterating the cubic gives `C_T ≤ r(δ)^(2^T)`; the final centering
   scalar `2/(1+a_T)` must be absorbed into the last stage, not counted as an
   additional cubic stage. For all T ≥ 0, the degree bound gives
   `r(δ)^(3^T) ≤ C_T`. In particular all these infima are strictly positive.
6. Show `C_0=1-δ`, `C_1<C_0`, and `C_(T+1)≤C_T²<C_T` for T ≥ 1. The middle
   inequality must follow by approximation of the infimum (or an equivalent
   epsilon argument), not by assuming a minimizing coefficient tuple exists.
7. Show `E_0=E_1=r(δ)`. At budget one arbitrary quadratic terms are allowed;
   only their odd parts are linear, so a degree-two lower bound by itself is
   insufficient for the exact small-budget equality.
8. For m ≥ 1, combine `C_m≤r(δ)^(2^m)≤E_m` for the upper stage bound. For m ≥ 2,
   put k=floor(m/2); prove `E_m≤C_k` by actual program inclusion. Strict decrease
   excludes every T<k. Handle m=0,1 separately and prove the final real casts and
   floor inequality for the advertised uniform constants.

## Computation reduction and LeanCert

No grid, subdivision, interval-size search or floating-point estimate is needed.
The crucial interval map can avoid calculus as well. With `t=sqrt(A/3)`:

- `x*(A-x²)-a*(1+a) = (x-a)*(1-x)*(x+a+1)`.
- `2*t³-x*(3*t²-x²) = (x-t)²*(x+2*t)`.

The factors have known signs on the full domain. Prove `A=3*t²`, `M=2*t³`, and
the strictly interior relation `a<t<1` from
`A-3*a²=(1-a)*(1+2*a)` and `3-A=(1-a)*(a+2)`.

The Chebyshev exterior comparison already exists in pinned Mathlib as the k=0
case of `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`,
applied to p and -p. Its evaluation at `(r+r⁻¹)/2` can be proved exactly from the
Chebyshev recurrence as `(r^D+r^(-D))/2`, avoiding logarithm/cosh computation.

Use LeanCert at pinned revision `621a43d7cf21f87872392a01e874f2f1dbddc926`,
Lean `leanprover/lean4:v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. Select kernel trust explicitly and
check every exported theorem with `#assert_trust kernel`. Pure algebra requires
no artificial interval computation. No proof may use `native_decide`, trust an
unverified numeric certificate, or import Challenge into Solution.

## Review and publication gates

The proposed public export list is `comparator.json`; it includes the actual
complete stage-count theorem, finite attainment, exact endpoint cases and all
major bridges. Comparator's `definition_names` is empty, and its permitted axioms
are only `propext`, `Classical.choice`, `Quot.sound` (or actual subsets).

Follow the repository's pinned Schiffer/Forsythe separation pattern, Tau Ceti
adapted multiple-referee protocol, and v0.4 formalization.yaml standard. AI-agent
reviews must be identified as such. Neither theorem-name matching nor a green
badge replaces inspection of definitions, source hashes and actual raw evidence.
Run authoritative type checks, proof builds, LeanCert, Comparator, default-kernel
replay and negative controls only on non-root Linux. Publish a separate complete
MF-02 PR only after all gates pass, retaining the permanent README target and
historical attribution, with updated Markdown/TeX/PDF/indexes and ID validation.
