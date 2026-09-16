# MI-04 repairs after actual run 35055219493

These two proof-body repairs address the exact observed Probes failures. They preserve every declaration header, all 21 full-target source files except the two local tactic/notation edits, and all ten frozen inputs. The complete before graph is bound to the real failed run, whose logs remain unchanged. Root is the implementation editor, not an independent referee of this patch. Independent review and actual fresh Linux elaboration remain required.
