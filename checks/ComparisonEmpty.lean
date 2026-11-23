import FLatticePaper.Plane.Induction.ComparisonEmpty

/-! Checks for task 70 part 2 (c): the concrete empty clause, the satisfiability form (W) and its transfer to the comparison fields,
and the forced monotonicity from (T) with the concrete empty clause. Each `#guard_msgs` fails unless the axioms are exactly the
standard three. -/
/--
info: 'FLatticePaper.Induction.not_emptyClause_of_sat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.not_emptyClause_of_sat

/--
info: 'FLatticePaper.Induction.hasSat_of_strict' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.hasSat_of_strict

/--
info: 'FLatticePaper.Induction.sat_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.sat_shift

/--
info: 'FLatticePaper.Induction.not_emptyClause_of_cmp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.not_emptyClause_of_cmp

/--
info: 'FLatticePaper.Induction.forced_contact_of_sat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.forced_contact_of_sat

/--
info: 'FLatticePaper.Induction.price_nonincrease_forced_of_sat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.price_nonincrease_forced_of_sat

/--
info: 'FLatticePaper.Induction.jplus_nonincrease_forced_of_sat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.jplus_nonincrease_forced_of_sat

/--
info: 'FLatticePaper.Induction.jminus_nonincrease_forced_of_sat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.jminus_nonincrease_forced_of_sat
