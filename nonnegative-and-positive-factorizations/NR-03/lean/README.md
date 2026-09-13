# NR-03 Lean proof candidate

This directory contains the statement boundary and an uncompiled proof
candidate for NR-03, “Full nonnegative rank of the quadratic correlation
matrix.” It is authored by **George
Stepaniants**, Department of Computing and Mathematical Sciences, California
Institute of Technology, Pasadena, California, USA. ChatGPT assistance is
disclosed. No email address is published.

The mathematical negative result is by **Sidney Holden**, Center for
Computational Biology, Flatiron Institute, Simons Foundation. The earlier
partial result by Matthew J. Colbrook is retained in the canonical problem
page and is not replaced by this formalization.

## Exact statement

`NLA.NR03.cMatrix n` is indexed by the full type `Fin n → Bool` on both sides
and has entry

```text
(1 - sum i, (a i as Real) * (b i as Real)) ^ 2
```

The subtraction is in `ℝ`, so intersections/dot products larger than one are
part of the prescribed matrix. `targetStatement` is exactly
`∀ n, 3 ≤ n → nonnegativeRank (cMatrix n) = 2 ^ n`.

`nonnegativeRank` is the minimum natural width of a factorization through
real entrywise-nonnegative matrices. Its definition is totalized with value
zero only when no finite factorization exists; the Challenge contracts expose
the attained-minimum and minimality semantics under the explicit existence
hypothesis. This is a rank definition, rather than a restricted support,
rational-only, or ordinary-rank proxy.

## Statement contracts and candidate proof

The package has ten deliberate contracts in `Challenge.lean`:

1. entrywise nonnegativity of every `cMatrix n`;
2. cardinality `Fintype.card (BoolVec 7) = 128`;
3. attained-minimum and minimality of `nonnegativeRank`;
4. the upper-bound bridge from a real factorization to the minimum;
5. the denominator/scaling bridge from an integer certificate to real factors;
6. a complete scaled integer certificate for `cMatrix 7` at width 127;
7. the resulting real width-127 factorization;
8. `nonnegativeRank (cMatrix 7) ≤ 127`;
9. strict failure of the claimed value `2^7 = 128`;
10. negation of the complete universal target at `n = 7`.

The scaled-certificate contract quantifies the full integer matrices and
positive denominators and asserts the entrywise identity. It contains no
trusted Python correctness premise. `Solution.lean` defines Holden's four
atom families directly and proves the Boolean-vector/mask correspondence
before constructing the matrices. The exact family identity is reduced to a
structural complementary-pair calculation and finite row-local arithmetic;
the retained JSON remains source data and is not imported as a correctness
axiom. Sparse data may guide proof development, but cannot replace the kernel
proof of every matrix entry.

`Challenge.lean` intentionally retains the ten statement contracts as the
Comparator boundary, so its bodies contain `sorry`. `Solution.lean` supplies
all ten corresponding theorem bodies and contains no `sorry`, `native_decide`,
or custom axiom. The candidate has not yet been elaborated under the
authoritative Linux LeanCert/Comparator harness; no Lean verification or
solved-status claim is made until that check and independent final reviews
pass.

## Local statement check

With the existing pinned dependency objects from another campaign package,
run:

```bash
NR03_DEP_ROOT=/path/to/existing/.lake/packages \
  python3 verification/statement-typecheck.py
```

The script invokes Lean 4.33.1 directly, checks clean pinned dependency
revisions, writes fresh objects and raw logs outside this package, and never
invokes Lake or downloads/builds dependencies. It is an elaboration check,
not a proof or a Linux Comparator run.

The proof candidate is intended for the pinned LeanCert kernel workflow. A
remote candidate run should invoke `lake build Solution`; the `Solution` Lake
library is registered and is the default target for that run. The ten
`#assert_trust kernel` and `#print axioms` commands at the end of
`Solution.lean` provide the per-export diagnostics required by the harness.
This package does not claim that command has passed.

A remote Linux run must check the full solution with the default kernel,
Comparator declarations, permitted axioms, and the repository's isolation
controls. Local proof compilation is currently paused because the constrained
development host exceeded its memory budget on an earlier exhaustive
reduction; no large local build artifacts are part of this package.

## Source identity

The canonical source base is commit
`50838e37dd793830e2cecd1055cfc7e0349490f1`. Exact source hashes and
author/target correspondence are recorded in `SOURCE_MAP.md` and
`NUMERICAL_TARGETS.md`.

The source-level candidate inventory, export list, and clean forbidden-token
scan are recorded in
[`reviews/proof-candidate-hashes.json`](reviews/proof-candidate-hashes.json).
That manifest intentionally excludes its own self-hash and records no build
result.
