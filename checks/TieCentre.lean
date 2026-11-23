import FLatticePaper.Plane.Induction.TieCentre

/-! Checks for task 72 (queue Q16, the tied centre): the axioms are as stated. -/
/--
info: 'FLatticePaper.Induction.retained_of_quota' does not depend on any axioms
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.retained_of_quota

/--
info: 'FLatticePaper.Induction.tie_sheetA_white' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.tie_sheetA_white

/--
info: 'FLatticePaper.Induction.sheetPolicyA_of_tie' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.sheetPolicyA_of_tie
