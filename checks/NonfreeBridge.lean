import FLatticePaper.Plane.Induction.NonfreeBridge

/-! Checks for task 72 (nonfree bridge): a nonfree site has a deck translate in the strict interior. Each `#guard_msgs` fails unless
the axioms are standard. -/
/--
info: 'FLatticePaper.Induction.nonfree_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.nonfree_bridge

/--
info: 'FLatticePaper.Induction.outside_SI_free' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.outside_SI_free
