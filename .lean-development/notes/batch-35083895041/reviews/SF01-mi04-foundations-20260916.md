# SF-01 independent partial-foundation review

Reviewer: `/root/mi04_independent_referee`, independent of author
`/root/ie13_continuation` and the other reviewer `/root`.

**Approve the exact first foundation batch for an actual pinned Linux
development build.** I found no mathematical error, weakened contract or
unproved premise hidden in a definition. This is source approval of five of
the 24 frozen contracts. The 19 remaining contracts, including the full Newton
theorem, remain unfinished. No new Lean, Lake, LeanCert or Comparator execution
occurred in this review; no problem or verified count is accepted.

The immutable author manifest is
`255e22740468918c517340b8792f0a775621db72929cc575973e6b6441a5c3cd`;
the nine-source closure is
`f0989a943e6c9dc47850ff36733ab2d692fcba69d623b2d0cc862b6fd2592213`.
I read all nine complete sources, all 24 current Challenge signatures, the
numerical boundary, status/reuse records, freeze and prior review chain,
complete original canonical statement and manuscript, and relevant pinned API
ranges. The separately executed static audit passed 91 checks and binds 86
inputs. It does not call a proof checker.

## Statement and mathematical review

The exact frozen Definitions and Challenge match the genuine statement build
at literal `09f9c4fd10c6e7d1efdb60eb0f43bc33ed920833`, run 35083895041,
including its input map and all 13 post-command maps. I read both complete
SF-01 logs: Definitions built and all 24 deliberately unproved statements
elaborated, each command exiting zero. Every focused log line also appears in
the retained raw job log in order. The overall development run failed in other
proof commands; those successful specifications are not proof evidence. The
copied freeze equals root's authorized isolated freeze. All nine frozen inputs
remain unchanged.

The original mathematical target is unchanged: every real matrix in every
dimension n >= 1, the spectral comparison-matrix H predicate, strictly positive
diagonal, initialization X_0=A, and the exact recurrence with X_k^-1 A at every
natural k. The supplied manuscript's wider scaling, affine initialization and
Halley results are not being claimed by this formalization. The new foundations
neither assume positive weights nor replace the complex spectral radius with
a norm bound, real-only spectrum or desired final result.

`Complexification` is a typed entrywise real-to-complex ring map. Identity,
subtraction, multiplication and scalar multiplication transports are correct.
Determinant transport has the proper orientation, and nonzero complexification
of a real determinant proves unit reflection. There is no assumed
nonsingularity and no dimension restriction on these elementary helpers.

`Spectrum` proves finiteness of the actual complex spectrum, then explicitly
constructs `Nonempty (Fin n)` from n >= 1 so the matrix algebra is nontrivial.
Algebraic closedness gives a nonempty spectrum. The image of the norm is a
finite nonempty subset of the reals; its conditional supremum is a member.
The extracted member proves attainment and nonnegativity, and the finite-set
upper-bound theorem supplies every spectral modulus bound. The subsequent
strict-bound contract uses that attained value. Thus the definition's sSup
does not exploit an empty-set default in a positive-dimensional conclusion.

`SpectralHomotopy` proves genuine unitness of sI-tB over the entire closed
interval [0,1], for arbitrary real B. From rho(B) < s it derives s > 0.
The t=0 branch is the invertible scalar identity. For t>0, t<=1 gives
s/t>=s; the positive real scalar s/t cannot lie in the complex spectrum.
The algebraic definition of spectrum therefore gives the corresponding complex
matrix unit, reflected to the real matrix by the determinant lemma. Multiplying
by the unit tI recovers exactly sI-tB. Scalar and matrix product order is
correct. Both endpoints, n=1, a zero matrix, repeated eigenvalues and nonnormal
matrices are covered, without an entrywise sign assumption on B. The explicit
division branch excludes t=0 before cancellation.

`Numerical` requests one exact LeanCert `interval_decide (trust := kernel)`
certificate for 0<1/2. Its proof is consumed both by coefficient halving and by
the two positive scalar fields of `initial_data_valid`; the empty pole and
weight families are discharged by `Fin.elim0`. The candidate does not import
LeanCert merely for appearance. There is no interval subdivision, sampled
matrix, numerical eigenvalue estimate or iteration enumeration. Execution of
this new certificate remains pending.

`WeightedZReuse` passes exactly the explicit real Z-matrix, positive-vector
and strictly positive image hypotheses to Sidney Holden's existing maximum
principle, unit and inverse-positivity lemmas. The last adapter uses that
proved unitness before simplifying the genuine inverse-times-one equation.
These helpers are also valid for an empty index type. They do not establish
either still-pending equivalence with the spectral M predicate; the supplied
weight is only a premise of these internal adapters. In particular, the
canonical theorem cannot obtain that weight from an assumed conclusion.

## Source integrity, reuse and scope

The five implementation headers equal their frozen Challenge signatures in
full, including hypotheses and quantifiers. There are exactly 16 additional
internal lemmas and 19 explicitly pending contracts. Every internal import
closes within the nine-source map; none imports Challenge. `FoundationChecks`
prints axioms and requests kernel trust for all five implemented contracts and
five key helpers. It is a partial build entry point, not a Solution. The
independent Comparator still names all 24 contracts, no definition holes and
only the three standard axioms. No complete-project Comparator result is
claimed. No source contains a proof hole, custom axiom, native proof mode,
unsafe implementation or resource increase.

All 12 relevant Mathlib primary files were rehashed against their exact
pinned Git objects. The separately retained IE13 half-certificate example
also matches its published Git object; its prior execution is a syntax/reuse
example only. I checked the actual mapMatrix/map_det, determinant-unit,
complex coercion/norm, finite/nonempty spectrum, finite supremum, spectrum
membership, scalar matrix product, matrix-vector product and inverse APIs.
The author's Minpoly inspection range 137-161 extends past that file's final
line 157. Its actual finite-spectrum theorem is at 149-152 and was read.
This nonsemantic range annotation is recorded in CHECKS; the author packet
has not been altered.

The two complete IV03 files and Apache-2.0 license equal literal original
commit `281f440650d174602120ca9b2b930d38f9fef205`. Their broader unused lemmas
were read as well; no additional IV03 success is substituted for SF01 proof.
Sidney Holden retains the reused formalization credit, Matthew J. Colbrook,
Cambridge DAMTP, retains original mathematical credit, and George Stepaniants,
Department of Computing and Mathematical Sciences, California Institute of
Technology, receives the new AI-assisted formalization credit. No contact
address appears in the candidate packet or current public-facing metadata.

This continues the prior independently sealed statement/preflight review and
its pinned Tau Ceti correctness, generality, proof-quality, reuse and attribution
standards. It is scoped agent review, not official Tau Ceti execution or human
peer review. The preserved Schiffer/Forsythe organization, numerical-first
boundary and draft formalization metadata remain bound; no new schema or
complete-manifest validation is asserted here. Historical draft/pending text
is distinguished from the later explicit PROOF-STATUS and authorized freeze.

The next gate is the actual shared Linux build of this exact partial closure,
followed by authenticated output and trust checks. Completing all 24 contracts,
full nonauthor final reviews, canonical kernel/Comparator controls and exact
publication/upstream runs are still required. Only this private review packet
was written; no author source, Git state, publication or count changed.
