import FLatticePaper.Plane.Induction.CollarStrict

/-! Checks for task 72 (hcollar, the collarBase split): the axioms are as stated. -/
/--
info: 'FLatticePaper.CollarStrict.hstrict_of_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.CollarStrict.hstrict_of_strong

/--
info: 'FLatticePaper.CollarStrict.hcollar_discharged' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.CollarStrict.hcollar_discharged

