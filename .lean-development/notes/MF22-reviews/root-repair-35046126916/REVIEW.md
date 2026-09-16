# MF-22 root independent eigenspace repair addendum

**APPROVE the exact ProjectorRank namespace repair as mathematical source.**
This extends my complete independent MF-22 source review and previous two-file
repair addendum. I remain a nonimplementer of its mathematical proof. The
candidate after-file is c0b2ed551c7b98b413ab5fa8efe60dc97509f5ef6b0edaa3bb64db3a600143c2.

I read the complete repaired file, exact three-expression diff and actual
compiler errors at Git64a04495, then inspected the pinned primary definition of
Module.End.eigenspace. It is the genuine subspace of vectors satisfying T v=z v.
The prior dot notation incorrectly searched the LinearMap namespace. Qualifying
the same intended eigenspace repairs two auxiliary header expressions and the
local E definition, without changing any scalar, matrix, dimension, quantifier,
assumption or intended conclusion. The old helper types had failed elaboration;
I do not claim an actual elaborated-term equality between old and new headers.

The existing proof still obtains a one-dimensional upper bound from a simple
characteristic root, puts every projector column into that actual eigenspace,
and derives vanishing two-by-two minors from a spanning vector. It imposes no
nonzero coordinate assumption. The boundary sandwich follows from these minors,
including the zero-projector-scalar case; the later independent coprimality
argument still proves the required nonzero scalar. No rank assumption was added.

All frozen definitions and 22 main contracts remain byte-identical. Exact
before bytes match the failed Git commit; after bytes differ by precisely the
three reviewed namespace qualifications. The full actual log and exact diff are
retained. The primary API files were compared directly to the pinned Mathlib
Git revision. No author/source mutation or local Lean/Lake execution occurred
in this review. Actual complete repaired compilation and all canonical
Comparator, default-kernel, axiom and operational controls remain pending.
