# MI-04: pinned Mathlib API audit before proof implementation

This is a read-only source audit, not an elaboration or verification receipt.
No Lean/Lake command, cache operation, proof implementation, or edit to the held
MI-04 package was performed. The two contracts audited are the full Hermitian
Rayleigh extremum/sandwich and normal-matrix unitary diagonalization. The exact
21-obligation package remains subject to root's second statement review and the
actual Linux declaration check.

The inspected Mathlib checkout is
`/tmp/nla-lean-mi22-worktree/matrix-inequalities-and-norms/MI-22/lean/.lake/packages/mathlib`,
whose actual `git rev-parse HEAD` is
`0df444a360eaa60ab8c11dca51a86af692955474`. All paths and line numbers below refer
to that revision. Signatures are quoted from source, with surrounding typeclass
assumptions stated separately; none is claimed to have been tested locally.

## Findings that affect implementation

1. The existing compactness and Rayleigh APIs suffice for the full unit-sphere
   extremum and positive operator norm. They do not supply our particular
   second-order sandwich: the explicit test-vector and weighted-square arguments
   remain genuine proof obligations.
2. The joint-eigenspace decomposition indexes **all** `ℂ × ℂ`, whereas
   `DirectSum.IsInternal.subordinateOrthonormalBasis` requires a **finite** index
   type. Do not apply those two APIs directly. Use
   `Module.End.Eigenvalues B × Module.End.Eigenvalues A`, which already has a
   noncomputable `Fintype` instance, and restrict the joint family. Zero
   intersections are permitted; eigenvalue multiplicities are retained inside
   the eigenspaces. No simple-spectrum assumption is necessary.
3. Mathlib's real Rayleigh quadratic is `re ⟪T x, x⟫`, while the frozen definition
   is `re ⟪x, T x⟫`. Bridge these with `inner_re_symm`; they are not syntactically
   identical. The matrix inner-product helper `Matrix.inner_toEuclideanCLM`
   is **real-only** and should not be used for the complex problem.
4. Keep using the explicit norm of `Matrix.toEuclideanCLM`; a bare matrix norm
   can select a different instance. The held definition already does this.

## Matrix, quadratic form, and positivity interfaces

`Mathlib/Analysis/CStarAlgebra/Matrix.lean:103–122`, under `[RCLike 𝕜]`,
`[Fintype n]`, and `[DecidableEq n]`, supplies:

```lean
def Matrix.toEuclideanCLM :
  Matrix n n 𝕜 ≃⋆ₐ[𝕜]
    (EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n)

lemma Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (A : Matrix n n 𝕜) :
  (Matrix.toEuclideanCLM A : _ →ₗ[𝕜] _) = Matrix.toEuclideanLin A

lemma Matrix.toEuclideanCLM_toLp (A : Matrix n n 𝕜) (x : n → 𝕜) :
  Matrix.toEuclideanCLM A (WithLp.toLp _ x) = WithLp.toLp _ (A *ᵥ x)

lemma Matrix.ofLp_toEuclideanCLM (A : Matrix n n 𝕜)
    (x : EuclideanSpace 𝕜 n) :
  WithLp.ofLp (Matrix.toEuclideanCLM A x) = A *ᵥ WithLp.ofLp x
```

The first map is a genuine star-algebra equivalence, so multiplication, scalar
multiplication, adjoints, and normality can be transported without a numerical
surrogate. The coercion equality is `rfl` in Mathlib, but introducing an explicit
typed intermediate map will make symmetry goals easier to elaborate.

`Mathlib/Analysis/InnerProductSpace/PiL2.lean:151,206,215–218` supplies
`EuclideanSpace.norm_sq_eq`, `finrank_euclideanSpace_fin`, and:

```lean
theorem EuclideanSpace.inner_eq_star_dotProduct
    (x y : EuclideanSpace 𝕜 ι) :
  inner 𝕜 x y = WithLp.ofLp y ⬝ᵥ star (WithLp.ofLp x)

lemma EuclideanSpace.inner_toLp_toLp (x y : ι → 𝕜) :
  inner 𝕜 (WithLp.toLp 2 x) (WithLp.toLp 2 y) = dotProduct y (star x)
```

The returned dot product places the unstarred vector first. Use
`dotProduct_comm` explicitly when matching `star x ⬝ᵥ (M *ᵥ x)`.

`Mathlib/Analysis/Matrix/Hermitian.lean:56–68`:

```lean
lemma Matrix.isSymmetric_toEuclideanLin_iff :
  A.toEuclideanLin.IsSymmetric ↔ A.IsHermitian

lemma Matrix.IsHermitian.im_star_dotProduct_mulVec_self
    (hA : A.IsHermitian) (x : n → 𝕜) :
  RCLike.im (star x ⬝ᵥ A *ᵥ x) = 0
```

An especially useful direct positivity bridge exists in
`Mathlib/Analysis/InnerProductSpace/Positive.lean:202–211`:

```lean
@[simp] theorem Matrix.isPositive_toEuclideanLin_iff
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} :
  A.toEuclideanLin.IsPositive ↔ A.PosSemidef
```

Here `LinearMap.IsPositive` is defined at lines 57–59 as
`IsSymmetric T ∧ ∀ x, 0 ≤ RCLike.re (inner 𝕜 (T x) x)`.
This can establish `positive_quadratic_iff` after the symmetry/coercion and
`inner_re_symm` bridges; it avoids manually unfolding the Finsupp definition of
matrix PSD. The existing lower-level alternative is
`Matrix.posSemidef_iff_dotProduct_mulVec` in
`Mathlib/LinearAlgebra/Matrix/PosDef.lean:297`.
Keep `open scoped ComplexOrder`, as in the held statements. This is the genuine
cone of nonnegative real complex numbers; no total order is being substituted.

Recommended explicit imports for the first proof module are
`Mathlib.Analysis.InnerProductSpace.Positive`,
`Mathlib.Analysis.InnerProductSpace.Rayleigh`, and the held Definitions module.
These are proof-module imports only; no frozen imports need modification.

## Full Rayleigh maximum and norm

`Mathlib/Analysis/InnerProductSpace/LinearMap.lean:265–286`:

```lean
def ContinuousLinearMap.reApplyInnerSelf (T : E →L[𝕜] E) (x : E) : ℝ :=
  RCLike.re (inner 𝕜 (T x) x)

theorem ContinuousLinearMap.reApplyInnerSelf_continuous (T : E →L[𝕜] E) :
  Continuous T.reApplyInnerSelf

theorem ContinuousLinearMap.reApplyInnerSelf_smul
    (T : E →L[𝕜] E) (x : E) {c : 𝕜} :
  T.reApplyInnerSelf (c • x) = ‖c‖ ^ 2 * T.reApplyInnerSelf x
```

`Mathlib/Analysis/InnerProductSpace/Rayleigh.lean:56,84,112–122`:

```lean
noncomputable abbrev ContinuousLinearMap.rayleighQuotient
    (T : E →L[𝕜] E) (x : E) := T.reApplyInnerSelf x / ‖x‖ ^ 2

theorem ContinuousLinearMap.image_rayleigh_eq_image_rayleigh_sphere
    (T : E →L[𝕜] E) {r : ℝ} (hr : 0 < r) :
  T.rayleighQuotient '' {0}ᶜ = T.rayleighQuotient '' Metric.sphere 0 r

theorem ContinuousLinearMap.rayleighQuotient_le_norm
    (T : E →L[𝕜] E) (x : E) : |T.rayleighQuotient x| ≤ ‖T‖

theorem ContinuousLinearMap.norm_eq_iSup_rayleighQuotient
    (T : E →L[𝕜] E) (hT : T.IsSymmetric) :
  ‖T‖ = ⨆ x, |T.rayleighQuotient x|
```

For the frozen `topValue = sSup rayleighValues`, use an attained maximum on the
compact unit sphere, instead of first converting to the library's indexed
supremum of eigenvalues. `IsCompact.exists_isMaxOn` is in
`Mathlib/Topology/Order/Compact.lean:248`; it requires a nonempty set and
`ContinuousOn`. The proof of
`LinearMap.IsSymmetric.hasEigenvalue_iSup_of_finiteDimensional` in
`Rayleigh.lean:326–340` is an existing example of this route. It installs
`FiniteDimensional.proper_rclike 𝕜 E` and uses `isCompact_sphere`.

Our `[Nonempty ι]` yields a unit coordinate vector, so the sphere is nonempty.
Identify `rayleighValues` with the continuous image of that sphere, obtain its
upper bound and maximum, then identify the maximum with `sSup` using
`IsLUB.csSup_eq` (`Mathlib/Order/ConditionallyCompleteLattice/Basic.lean:217`).
Do not apply real `csSup` rules without their boundedness/nonemptiness arguments.
For `positive_norm_eq_top`, positivity makes each real Rayleigh quotient
nonnegative, so the absolute value in `norm_eq_iSup_rayleighQuotient` disappears.
The zero vector contributes zero and is handled separately; every other vector
is normalized onto the sphere. These arguments also cover a zero PSD matrix.

## Exact sandwich: remaining proof work and economical interfaces

Let `g j = 1 - d j`, `M = spectralNorm V`, and let `w` be the frozen correction
vector. The assumptions give `g j ≥ 1/2` for `j ≠ a` and, for the upper estimate,
`g j - ε*M > 1/4`. Establish these denominator facts before algebraic rewrites.
No lower bound on `d j` is required.

The lower test vector is the literal `e_a + (ε : ℂ) • w`, with squared norm
`1 + ε²‖w‖²`. Its quadratic numerator is
`1 + ε²(‖w‖² + secondCoefficient d V a) + ε³ realQuadratic V w`.
Subtracting its squared norm gives the exact lower numerator from Challenge.
Normalize by the positive square root or use a previously proved homogeneous
Rayleigh bound; the latter can reduce square-root bookkeeping.

For the upper estimate, decompose every unit vector as `c*e_a + r`, where
`r a = 0`. Bound the `V`-quadratic on `r` by `M‖r‖²`. For each off-peak coordinate,
apply the scalar weighted-square inequality with the positive denominator
`g j - ε*M`; sum it once. Finally use `‖c‖² ≤ 1`. This proves a bound for **every**
unit vector and hence for the attained top value. It must not be replaced by a
test-vector-only bound.

Useful exact scalar interfaces are `Complex.normSq_nonneg`,
`Complex.normSq_add`, `Complex.normSq_sub`, `Complex.normSq_mul`, and
`Complex.normSq_div` in `Mathlib/Data/Complex/Basic.lean`, together with
`Complex.normSq_eq_norm_sq` in `Mathlib/Analysis/Complex/Norm.lean:147`.
Prove the one-coordinate weighted-square identity once, using real/imaginary
parts if necessary. Avoid expanding generic `Fin n` sums or all matrix entries.
The resulting proof is symbolic in dimension and needs no interval subdivision
or eigenvalue approximation.

For the right-limit result, use continuity of finitely many scalar denominators
and the two explicit bounds. The current finite-sum continuity API uses
`tendsto_finsetSum`; the older `tendsto_finset_sum` is deprecated. The eventual
squeeze is `tendsto_of_tendsto_of_tendsto_of_le_of_le'`, alias
`Filter.Tendsto.squeeze'`, in `Mathlib/Topology/Order/Basic.lean:225`.
The right-neighborhood filter has its `NeBot` instance from `nhdsGT_neBot` in
`Mathlib/Topology/Order/DenselyOrdered.lean:220`. Explicitly restrict to the
eventual positive/small interval before using the sandwich.

## Normal complex matrices: complete finite joint-eigenbasis route

There was no direct general-normal-matrix diagonalization theorem identified in
the inspected Matrix/InnerProductSpace source. The Hermitian spectral theorem
cannot be applied to a general normal `X`. The available joint-eigenspace route
is sufficient and includes singular matrices and repeated values.

In `Mathlib/LinearAlgebra/Complex/Module.lean:391–416,586–595`, `realPart` and
`imaginaryPart` are **global** declarations, not `Complex.realPart`:

```lean
noncomputable def realPart : A →ₗ[ℝ] selfAdjoint A
noncomputable def imaginaryPart : A →ₗ[ℝ] selfAdjoint A

theorem realPart_add_I_smul_imaginaryPart (a : A) :
  (realPart a : A) + Complex.I • (imaginaryPart a : A) = a

lemma isStarNormal_iff_commute_realPart_imaginaryPart {x : A} :
  IsStarNormal x ↔ Commute (realPart x : A) (imaginaryPart x : A)
```

Use explicit type annotations for the two `selfAdjoint` coercions. The optional
notations `ℜ` and `ℑ` require `open scoped ComplexStarModule`. This import should
be made explicit in the normality proof module. Work either on matrices and
transport through the star-algebra equivalence, or directly on the continuous
linear operator. For the latter,
`ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`
(`Analysis/InnerProductSpace/Adjoint.lean:380`) supplies symmetry of the
underlying linear maps. `Matrix.isHermitian_iff_isSelfAdjoint` is in
`LinearAlgebra/Matrix/Hermitian.lean:51` for the former.

For symmetric commuting linear maps `A B : E →ₗ[𝕜] E`, the exact declarations in
`Mathlib/Analysis/InnerProductSpace/JointEigenspace.lean:61,101,110` are:

```lean
theorem LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
  OrthogonalFamily 𝕜
    (fun i : 𝕜 × 𝕜 =>
      (Module.End.eigenspace A i.2 ⊓ Module.End.eigenspace B i.1 : Submodule 𝕜 E))
    (fun i => (Module.End.eigenspace A i.2 ⊓ Module.End.eigenspace B i.1).subtypeₗᵢ)

theorem LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
  (⨆ α, ⨆ γ, Module.End.eigenspace A α ⊓ Module.End.eigenspace B γ) = ⊤

theorem LinearMap.IsSymmetric.directSum_isInternal_of_commute
    (hA : A.IsSymmetric) (hB : B.IsSymmetric) (hAB : Commute A B) :
  DirectSum.IsInternal
    (fun i : 𝕜 × 𝕜 => Module.End.eigenspace A i.2 ⊓ Module.End.eigenspace B i.1)
```

The last two require `[FiniteDimensional 𝕜 E]`. Notice the reversed pair order
in the family (`A i.2`, `B i.1`). Maintain this consistently.

`Mathlib/LinearAlgebra/Eigenspace/Minpoly.lean:101–109` supplies
`Module.End.finite_hasEigenvalue` and the noncomputable instance
`Fintype f.Eigenvalues` for finite-dimensional vector spaces. Thus set
`J = Module.End.Eigenvalues B × Module.End.Eigenvalues A` and
`V j = eigenspace A j.2.val ⊓ eigenspace B j.1.val`.
Restrict the orthogonal family using `OrthogonalFamily.comp` from
`Analysis/InnerProductSpace/Subspace.lean:150` and the injective product of the
two subtype inclusions.

The supremum of `V` is still top: an omitted pair has at least one zero
eigenspace, hence a zero intersection. This can be proved with two explicit
`iSup_le`/`le_iSup_of_le` arguments and cases on `HasEigenvalue`, or with
`iSup_subtype` and `iSup_ne_bot_subtype`
(`Order/CompleteLattice/Basic.lean:451,775`). Then
`OrthogonalFamily.isInternal_iff`
(`Analysis/InnerProductSpace/Projection/FiniteDimensional.lean:265`)
converts orthogonality plus top span into a finite-index internal direct sum.
This small restriction bridge is new proof work, not a library theorem being
assumed.

`Mathlib/Analysis/InnerProductSpace/PiL2.lean:1097–1126` then supplies, under
`[Fintype J] [DecidableEq J] [FiniteDimensional 𝕜 E]`,
`hn : Module.finrank 𝕜 E = n`, `hV : DirectSum.IsInternal V`, and
`hV' : OrthogonalFamily 𝕜 (fun i => V i) (fun i => (V i).subtypeₗᵢ)`:

```lean
hV.subordinateOrthonormalBasis hn hV' : OrthonormalBasis (Fin n) 𝕜 E
hV.subordinateOrthonormalBasisIndex hn a hV' : J
hV.subordinateOrthonormalBasis_subordinate hn a hV' :
  hV.subordinateOrthonormalBasis hn hV' a ∈
    V (hV.subordinateOrthonormalBasisIndex hn a hV')
```

The `[Fintype J]` requirement is inherited from the file-level variable at
`PiL2.lean:388`; it is easy to miss when reading only the local declaration.
The membership gives both eigenvector equations through
`Module.End.mem_eigenspace_iff`
(`LinearAlgebra/Eigenspace/Basic.lean:449`). Recombine them using
`realPart_add_I_smul_imaginaryPart` to get the eigenvalue of `X`.

Build the matrix whose columns are this orthonormal basis. The exact existing
pattern is `Matrix.IsHermitian.eigenvectorUnitary` in
`Analysis/Matrix/Spectrum.lean:89–113`, using
`(EuclideanSpace.basisFun (Fin n) ℂ).toBasis.toMatrix b.toBasis` and
`OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary`
(`PiL2.lean:963`). Prove the diagonalization columnwise, and use
`Unitary.coe_star_mul_self` / `Unitary.coe_mul_star_self` to obtain precisely
the frozen orientation `X = U * diagonal z * U.conjTranspose`.

This construction neither divides by an eigenvalue nor chooses a one-dimensional
eigenspace. It therefore covers zero eigenvalues, repeated real/imaginary parts,
arbitrary intersections, scalar matrices, and dimension one without added
hypotheses. No explicit characteristic polynomial or eigenvalue computation is
needed.

## Statement elaboration and source identity

No mathematical statement amendment is recommended by this audit. Existing
frozen-style definitions use explicit matrix/Euclidean-space types and the
necessary complex-order scope. Genuine elaboration hazards to check remotely
are the `Matrix.unitaryGroup` coercions, optional type arguments for
`toEuclideanCLM`, `Nonempty (Fin n)` derived from `hn : 1 ≤ n` inside proofs,
and `Fintype` synthesis for the finite joint-eigenvalue index. The finite
dimensional/proper-space instances should be installed explicitly where
compactness needs them rather than relying on a long typeclass search.

Before completing this note, every one of the 27 held files matched
`MI-04/DRAFT-CHECKS.json`, SHA256
`1d0680862f81dec0e9c419e3d7351c3d431f4439a09d56fee3ca10761d527b3b`.
In particular:

| Held file | SHA256 |
| --- | --- |
| `NLA/MI04/Definitions.lean` | `cfd0c1e0174699e8e9127a6fb8b7ce9de3f4c7d9770292746d15c0a5bc047748` |
| `Challenge.lean` | `ca80d090bfe9f3013d08aa86297761e1e524810881bce92776896545d6eeabf9` |
| `NUMERICAL_TARGETS.md` | `5cb5e20ffcf035b2ea303cf9edae2e85619b0f562bf302cf6df0c7a46079d1d7` |

The separate independent elimination statement approval received during this
audit is `reviews/MI04-elimination-statements/REVIEW.md`, SHA256
`9d7012d31858b44797f1577c002ca65511664a6f7000bac1ea893f6a40f03586`.
It is a source-level approval. This note makes no claim of Linux elaboration,
proof completion, canonical Comparator acceptance, or publication.
