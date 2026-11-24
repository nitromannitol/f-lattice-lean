import FLatticePaper.Plane.Induction.TwosZeroEven

/-! Checks for task 72 (the even zero line of the twos base, from the one-point odd seed): the axioms are standard. -/
/--
info: 'FLatticePaper.Induction.twos_seed_value' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.twos_seed_value

/--
info: 'FLatticePaper.Induction.twos_hseed' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.twos_hseed

/--
info: 'FLatticePaper.Induction.twos_zeroEvenLine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.twos_zeroEvenLine
