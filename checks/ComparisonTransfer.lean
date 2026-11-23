import FLatticePaper.Plane.Induction.ComparisonTransfer

/-! Checks for task 70 part 2 (c): `P`, `J₊`, `J₋` do not increase along black and forced white edges, from the named
hypotheses (T) and (W) for the forced white edges. Each `#guard_msgs` fails unless the axioms are exactly the standard three
(propext, Classical.choice, Quot.sound). -/
/--
info: 'FLatticePaper.Induction.price_nonincrease_black' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.price_nonincrease_black

/--
info: 'FLatticePaper.Induction.jplus_nonincrease_black' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.jplus_nonincrease_black

/--
info: 'FLatticePaper.Induction.jminus_nonincrease_black' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.jminus_nonincrease_black

/--
info: 'FLatticePaper.Induction.price_nonincrease_forced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.price_nonincrease_forced

/--
info: 'FLatticePaper.Induction.jplus_nonincrease_forced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.jplus_nonincrease_forced

/--
info: 'FLatticePaper.Induction.jminus_nonincrease_forced' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.jminus_nonincrease_forced
