# IE-13 independent generic-prefix proof review

**APPROVE the four-module mathematical source prefix**, at the exact hashes in CHECKS.json. No mathematical or concrete API correction is requested. This covers six frozen exports, not the complete 28-obligation problem; these new proof files have not yet been compiled. I did not contribute to their implementation.

## Scope, boundary and provenance

I read the full canonical IE-13 target and manuscript at ce47b5630bf3680d9211131c3a43825b022c139a, the frozen Definitions/Challenge, all four complete Basic/Maxima/GEPP/Prefix sources, and the explicit reuse records. The original problem requires the sharp all-dimensional bound for arbitrary unequal lower/upper bandwidths, nonsingular complex matrices and every legal maximal-modulus tie path in the original ordering. The prefix preserves that model but does not yet prove the general-band front, envelope, zero-bandwidth conclusions, rational witnesses or sharp supremum.

All six exposed signatures match the frozen contracts exactly after whitespace normalization. All ten frozen inputs are unchanged. Freeze 85916aae89eb2111ff914b8767e8918548c132a6ff6c7ed92e52286bec1998fe binds the successful IE-13 Definitions and 28-statement components of actual Linux run 35048156414, whose overall workflow failed on other projects. I independently checked the two component command records, log hashes and unchanged pre/post definition/Challenge hashes. Intentional Challenge holes are not proofs.

Basic and GEPP are attributed adaptations of the accepted IE-14 generic complex GEPP code at 6e48f25fffdae2cf93e4985dc515abbd15e0481b. I retrieved and hashed both original files from Git, and compared their generic proof bodies byte-for-byte: Basic changes only the shorter maximum theorem's name; GEPP's copied generic body is unchanged. The explicit namespace/import/configuration/attribution changes and the new exact-contract wrapper are separate. No IE-14 two-row front, cyclic witness, Fibonacci bound or problem-specific theorem is imported. Earlier IE-05 provenance and original Matthew J. Colbrook/Cambridge credit remain explicit; George Stepaniants/Caltech CMS formalization credit has no contact email.

## Finite maxima and literal algorithm

The model bridge unfolds the actual current-row swap and trailing Schur update, starts at A, and retains fixed original column order. The entry maximum and every nonempty active maximum are attained finite suprema of complex moduli. Nonnegative inactive padding cannot increase an active maximum; the active set contains (k,k). Positive dimension and nonsingularity imply a positive original maximum by excluding the zero matrix. The growth proof then divides by this established positive quantity, bounds every active entry at every Fin n stage and exhibits an attaining stage/entry. Its strongest valid form does not need path admissibility, because these are direct maximum semantics. Stage zero includes A and stage n−1 includes the final scalar.

## Genuine GEPP existence and arbitrary-prefix completion

ActiveInjective is exactly injectivity of the active column-to-row block, encoded with vectors supported at columns at least k. The initial property comes from the genuine nonsingular matrix, not an assumed path certificate. If the active pivot column vanished, its basis vector would contradict this injectivity. Row swaps confined to active rows preserve it. For the Schur step, the constructed y=x+c e_k, with c=−(Bx)_k/B_kk, vanishes on all active rows precisely when the next Schur block kills x. The nonzero pivot justifies that cancellation; injectivity forces y=0, while x_k=0 and off-k coordinates recover x=0. This works over ℂ without positivity or real-entry assumptions.

The selector takes a maximum over the actual finite active pivot column. Active injectivity ensures this maximum is positive, hence its selected entry is nonzero. Classical choice selects one allowable suffix only for existence; the public AdmissiblePivot and AdmissiblePath predicates still permit every largest-modulus tie.

Prefix completion uses the supplied pivot at each k<t and a genuine maximizing pivot afterward. The helper trajectory_agree_before proves a state at s depends only on choices with k<s. Therefore completedPath agrees with every original choice before t and every original trajectory state for s≤t. No validity of the supplied unused suffix is assumed.

The mixed trajectory remains active-injective by induction. Before t, the prior-state equality transports precisely the original admissible-prefix hypothesis; at and after t, active injectivity supplies a maximizing nonzero pivot. This establishes full path admissibility. For t=0 the prefix condition is empty and the construction is a genuine maximum-pivot path with unchanged input state. For t=n all physical pivot choices are already fixed; the construction preserves them and the complete state at n as well. The same proof covers every intermediate t and s=t. The unused hn/ht in the final wrapper are harmless: its helper result is stronger, not a missing endpoint assumption.

## Proof quality and remaining work

I inspected the pinned finite-maximum, matrix-injectivity, basis-vector action and swap APIs. This prefix uses finite sums and exact complex field algebra, with no numerical interval subdivision or unnecessary matrix enumeration. All six public exports retain kernel LeanCert assertions; no deliberate hole, new axiom, Challenge import or native-decide proof occurs in the four files. These are source observations, not a transitive runtime axiom audit.

Remote compilation of this prefix, the remaining 22 mathematical exports, independent full-proof review and canonical kernel/Comparator/negative-control gates remain required. No local Lean or Lake was run; no author source, workflow, repository status or verified count was changed.
