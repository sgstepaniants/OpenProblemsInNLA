# MF-22 bounded static tail API preflight

Source-only preflight of Dominant, SpectralTailBounds, GreenEntryBounds and Conditioning against the pinned Mathlib and already compiled project helpers. These modules were blocked by ProjectorRank in actual run 35048156414; no actual diagnostic or compiler acceptance is claimed for this predictive edit. No Lean or Lake was run locally.

## One concrete correction

SpectralTailBounds uses `add_le_add_right h c` to add a fixed term on the right. Pinned Mathlib/Algebra/Order/Monoid/Unbundled/Basic.lean:69-71 generates the additive theorem from `mul_le_mul_right`; its result places the fixed term on the left. The dual naming convention is confirmed by the genuine earlier MI-04 Rayleigh diagnostic in run 35046126916: `add_le_add_left h c` produced `a+c ≤ b+c`, while `c+a ≤ c+b` was requested.

The one-line correction uses `add_le_add (spectralNorm_add _ _) (le_refl _)`, explicitly establishing `(‖A‖ + ‖B‖)` as the first varying summand and leaving the last norm fixed. The conclusion, all definitions, declaration headers, assumptions, coefficient values and 22 frozen exports are unchanged.

## Concerns checked without changes

- `scalar_eq_smul_one` is the local NLA.MF22 helper already accepted in TransferCertificates:108, imported transitively through SpectralAlgebra. Its absence from Mathlib is not an error. Dominant is unchanged.
- Matrix.eval_charpoly, adjugate multiplication identities and trace cyclicity have the expected namespace, arguments and orientation.
- The remainder powers use the pinned nonnegative-base `pow_le_one₀` and genuine complex norm powers. The reverse scalar-decomposition rewrite contains rho and the full roots family on its matching right side.
- GreenEntryBounds supplies rho and roots explicitly to the actual five-term expansion, uses the accepted scalar coefficient estimates, and retains every finite source index.
- Conditioning's conjunction projections match the accepted five-part Green inverse theorem; the full 2n-dimensional operator norm bounds, cast arithmetic and Real.rpow_two preserve exponent 2 and the complete original existential target.

No additional concrete defect was identified in this bounded source check. This is neither an assurance that the tail will elaborate nor a replacement for the required remote compiler, kernel and Comparator gates.
