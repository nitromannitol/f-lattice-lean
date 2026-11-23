import FLatticePaper.CanonicalHeadline

/-! Checks for task 72 (nonfree roots): the W1Forced root condition of the drop lemma, the uniqueness of the retained input at a forced
white (derived from the canonical policy), and the headline. Each `#guard_msgs` fails unless the axioms are standard. -/
/--
info: 'FLatticePaper.Induction.nonfree_root_forced' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.nonfree_root_forced

/--
info: 'FLatticePaper.Induction.forcedWhiteUnique_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.forcedWhiteUnique_of_canonical

/--
info: 'FLatticePaper.odometersTheorem_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.odometersTheorem_of_canonical
