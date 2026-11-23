import FLatticePaper.Plane.Induction.NeighbourDrop

/-! Checks for task 72 (the neighbour zero and the regular H drop): the axioms are as stated. -/
/--
info: 'FLatticePaper.Induction.evenSite_add_vec_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.evenSite_add_vec_iff

/--
info: 'FLatticePaper.Induction.odd_neighbour_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.odd_neighbour_strip

/--
info: 'FLatticePaper.Induction.even_neighbour_window' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.even_neighbour_window

/--
info: 'FLatticePaper.Induction.H_drop_regular' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.H_drop_regular
