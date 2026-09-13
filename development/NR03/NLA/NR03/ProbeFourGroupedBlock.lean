/-
NR-03 grouped closed-row benchmark: rows 120 through 127, every column.
Each literal row is checked by a separate closed kernel decision before the
same previously frozen block predicate is assembled using finite cases.
See grouped-row-probe/PROBES.md. This is not complete NR-03 verification.
-/
import NLA.NR03.FamilyDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace NLA.NR03.GroupedProbe.Four

theorem row120 : ∀ b : Mask7,
    fourSum (120 : Mask7) b = fourClosed (120 : Mask7) b := by
  decide +kernel

#print axioms NLA.NR03.GroupedProbe.Four.row120

theorem row121 : ∀ b : Mask7,
    fourSum (121 : Mask7) b = fourClosed (121 : Mask7) b := by
  decide +kernel

#print axioms NLA.NR03.GroupedProbe.Four.row121

theorem row122 : ∀ b : Mask7,
    fourSum (122 : Mask7) b = fourClosed (122 : Mask7) b := by
  decide +kernel

#print axioms NLA.NR03.GroupedProbe.Four.row122

theorem row123 : ∀ b : Mask7,
    fourSum (123 : Mask7) b = fourClosed (123 : Mask7) b := by
  decide +kernel

#print axioms NLA.NR03.GroupedProbe.Four.row123

theorem row124 : ∀ b : Mask7,
    fourSum (124 : Mask7) b = fourClosed (124 : Mask7) b := by
  decide +kernel

#print axioms NLA.NR03.GroupedProbe.Four.row124

theorem row125 : ∀ b : Mask7,
    fourSum (125 : Mask7) b = fourClosed (125 : Mask7) b := by
  decide +kernel

#print axioms NLA.NR03.GroupedProbe.Four.row125

theorem row126 : ∀ b : Mask7,
    fourSum (126 : Mask7) b = fourClosed (126 : Mask7) b := by
  decide +kernel

#print axioms NLA.NR03.GroupedProbe.Four.row126

theorem row127 : ∀ b : Mask7,
    fourSum (127 : Mask7) b = fourClosed (127 : Mask7) b := by
  decide +kernel

#print axioms NLA.NR03.GroupedProbe.Four.row127

theorem high_rows : ∀ (r : Fin 8) (b : Mask7),
    fourSum (Fin.natAdd 120 r) b =
      fourClosed (Fin.natAdd 120 r) b := by
  intro r
  fin_cases r
  · exact row120
  · exact row121
  · exact row122
  · exact row123
  · exact row124
  · exact row125
  · exact row126
  · exact row127

#print axioms NLA.NR03.GroupedProbe.Four.high_rows

end NLA.NR03.GroupedProbe.Four
