/-
NR-03 restricted development probe: rows 120 through 127, every column.
The complete family theorem and original ten-export boundary are unchanged.
See family-probe/PROBES.md for the statements fixed before this implementation.
This helper is not a full-family or full-problem verification claim.
-/
import NLA.NR03.FamilyDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace NLA.NR03.Probe

theorem pair_high_rows : ∀ (r : Fin 8) (b : Mask7),
    pairSum (Fin.natAdd 120 r) b =
      pairClosed (Fin.natAdd 120 r) b := by
  decide +kernel

end NLA.NR03.Probe

#print axioms NLA.NR03.Probe.pair_high_rows
