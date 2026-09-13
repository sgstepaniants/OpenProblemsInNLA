/-
NR-03 single-row development probe: fixed row 120, every column.
The full-family theorems and ten-export problem boundary remain unchanged.
See single-row-probe/PROBES.md for statements fixed before implementation.
This helper is not a full-family or full-problem verification claim.
-/
import NLA.NR03.FamilyDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace NLA.NR03.Probe

theorem four_row120 : ∀ b : Mask7,
    fourSum (120 : Mask7) b = fourClosed (120 : Mask7) b := by
  decide +kernel

end NLA.NR03.Probe

#print axioms NLA.NR03.Probe.four_row120
