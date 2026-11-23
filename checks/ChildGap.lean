import FLatticePaper.Plane.Induction.ChildGap

/-! Checks for task 72 / Q20 (the child gap of a word, scope): the axioms are as stated. -/
/--
info: 'FLatticePaper.ChildGap.child_gap_ge_four' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.ChildGap.child_gap_ge_four

/--
info: 'FLatticePaper.ChildGap.child_gap_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.ChildGap.child_gap_eq

/--
info: 'FLatticePaper.ChildGap.walk_inv' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.ChildGap.walk_inv

/--
info: 'FLatticePaper.ChildGap.walk_nontwo' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.ChildGap.walk_nontwo

/--
info: 'FLatticePaper.ChildGap.walk_two' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.ChildGap.walk_two

