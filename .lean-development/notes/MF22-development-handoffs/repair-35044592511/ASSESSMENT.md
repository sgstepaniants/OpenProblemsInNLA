# MF-22: proof-only repair after actual run 35044592511

The actual Linux build at `cc17d70a568de50bb428f2665f576aec9dcd884e` accepted GreenKernel, GreenCoefficients, TransferCertificates and GreenInverse. It rejected GreenEntryAlgebra at line 56 in both branches: the subsequent `module` normalization exposed unmatched transfer-power atoms. The diagnostic expressly marked the unspecialized `transfer_power_decomposition` rewrite unused. Its `roots` argument occurs only on the right side, so that simp invocation could not infer the intended root family from a left side `transferMatrix ρ ^ j`.

The only change supplies the already-fixed `ρ roots` arguments to that same identity. This enables the exact decomposition before matrix distributivity, the already-assumed boundary sandwich and scalar module normalization. It changes no expression, theorem type, assumption, coefficient, exponent, dimension, norm or bound. No new mathematical premise or tactic fallback is introduced. All declaration headers and the other 28 definition/proof/entrypoint files remain byte-identical.

The before file was compared directly with the actual Git source, not reconstructed from the diagnostic. The authentic full build log, exact before/after files, one-line diff, complete 29-file prior/current maps and prior independent mathematical approval are retained. The separate ProjectorAlgebra error is owned by the elimination agent and is not repaired here.

This is an author source/API assessment, not an independent approval or a Lean acceptance claim. No Lean/Lake command ran locally. The repaired expression needs the next actual Linux check and two independent final-referee diff reconciliations.
