import FLatticePaper.Plane.Induction.TwosTileCover

/-! Checks for task 72 (the native tile of the twos standard field and the three-shift cover): the axioms are standard. -/
/--
info: 'FLatticePaper.Induction.standardField_twos_eq_tile' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.standardField_twos_eq_tile

/--
info: 'FLatticePaper.Induction.twos_shift_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.twos_shift_cover
