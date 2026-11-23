import FLatticePaper.Plane.Induction.EdgeDrop

/-! Checks for task 72 (the H drop along an edge with the sharp band): the axioms are as stated. -/
/--
info: 'FLatticePaper.Induction.edge_step_parent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.edge_step_parent

/--
info: 'FLatticePaper.Induction.edge_parity_flip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.edge_parity_flip

/--
info: 'FLatticePaper.Induction.evenSite_sub_even_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.evenSite_sub_even_iff

/--
info: 'FLatticePaper.Induction.H_drop_edge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.H_drop_edge
