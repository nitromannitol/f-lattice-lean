import FLatticePaper.Plane.Induction.CutTipEscape

/-! Checks for task 72 (TIP_THEOREM, the two-edge cut-tip escape): the axioms are as stated. -/
/--
info: 'FLatticePaper.escape_one_of_white' does not depend on any axioms
-/
#guard_msgs in
#print axioms FLatticePaper.escape_one_of_white

/--
info: 'FLatticePaper.two_edge_escape' does not depend on any axioms
-/
#guard_msgs in
#print axioms FLatticePaper.two_edge_escape

/--
info: 'FLatticePaper.tip_W0_escape' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.tip_W0_escape

/--
info: 'FLatticePaper.tip_W1_escape' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.tip_W1_escape
