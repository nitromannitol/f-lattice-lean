import FLatticePaper.Plane.Induction.MinAdmission

/-! Checks for task 72 / Q20 (the minimum admission of the two-rank argument): the axioms are as stated. -/
/--
info: 'FLatticePaper.MinAdmission.min_lap_local' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.MinAdmission.min_lap_local

/--
info: 'FLatticePaper.MinAdmission.laplacian_min_local' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.MinAdmission.laplacian_min_local

/--
info: 'FLatticePaper.MinAdmission.min_field_binary' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.MinAdmission.min_field_binary
