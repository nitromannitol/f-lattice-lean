import FLatticePaper.Plane.Induction.MinPolicy

/-! Checks for task 72 / Q20 (the acyclic minimum policy, MinPolicy.lean): the axioms are as stated. -/
/--
info: 'FLatticePaper.MinPolicy.msel_squareClauses' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.MinPolicy.msel_squareClauses

/--
info: 'FLatticePaper.MinPolicy.lapM_binary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.MinPolicy.lapM_binary

/--
info: 'FLatticePaper.MinPolicy.tie_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.MinPolicy.tie_arith
