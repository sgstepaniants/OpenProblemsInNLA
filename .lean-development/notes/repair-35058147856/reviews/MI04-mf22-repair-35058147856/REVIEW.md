# MI-04: independent BasisTransport repair approval

**Approve the three bounded proof-body repairs**, with fresh complete Linux execution still pending. I did not implement the repairs, edit any proof, or run Lean. I read the entire current 99-line `BasisTransport.lean`, its exact patch, the relevant actual failure diagnostics and the pinned primary Mathlib API definitions. My earlier complete 21-file mathematical source review remains applicable to the other unchanged files.

The reviewed current closure is **0739d4df0299ae9be0f03aa20c71e9c96f8875a8384bc39897dc497677e9d81c**, from `repair-35058147856-provenance`. This metadata clarification supersedes `0b3840f3…`; its mathematical source predecessor is **3f553e70…**, the closure covered by my prior complete review. The original repair packet remains intact at manifest **38c1c42a…**. The provenance amendment corrects inherited remarks about the earlier Probes repair and does not change any mathematical or frozen input.

The previous [run 35058147856](https://github.com/sgstepaniants/OpenProblemsInNLA/actions/runs/35058147856/job/104672556977), commit `d36c8b357347a78781e854328a95fd5e4adce852`, actually failed in `BasisTransport`. Its receipt, archive, raw job lines and exact pre-repair Git inputs agree. The module's unfinished terms produced `sorryAx`, and the trust assertion correctly rejected them. That failure is not successful proof evidence.

The repair addresses each observed issue directly:

1. The two same-vector orthonormality cases had residual unit-norm goals. Adding the already available assumptions `hu : ‖u‖ = 1` and `hv : ‖v‖ = 1` to the final simplification discharges these cases. This adds no premise. The mixed-vector cases retain the supplied orthogonality and derived distinctness.
2. The pinned API defines `toMatrix_apply` in namespace **Module.Basis**. Qualifying that name recovers the exact entry formula. Together with the orthonormal-basis representation and coordinate basis lemmas, it gives the unchanged equality `(basisUnitary B) i j = B j i`.
3. The reverse rewrite previously presented an unconstrained matrix-entry metavariable. Supplying `unitarySimilarity X (basisUnitary B)`, `i`, and `j` instantiates the existing coordinate-coefficient identity before rewriting. The subsequent unitary-action identities establish the same desired coefficient in basis `B`.

The complete basis-extension argument still extends an arbitrary orthonormal pair, constructs its actual unitary change-of-basis matrix, transports the entry symmetry and obtains equality of norms from equality of their squares and nonnegativity. No dimension-two exception, coordinate-basis restriction, added hypothesis or altered conclusion appears. All three retained primary source files match Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474` exactly.

I independently reconciled all **21 active source files** with my prior review and the failed receipt/Git source: only `BasisTransport.lean` differs, by exactly the three displayed substitutions. All ten frozen inputs, all declaration headers and all 21 Comparator target declarations are unchanged. The existing LeanCert and trust settings are unchanged. Original mathematics remains attributed to Matthew J. Colbrook, and the formalization to George Stepaniants, Caltech's Department of Computing and Mathematical Sciences.

This is source and repair approval, **not** a successful checker-run claim. A complete repaired-source Linux build, all 21 actual Comparator/default-kernel/axiom checks, required per-project controls and final publication review remain necessary before marking this formalization verified.
