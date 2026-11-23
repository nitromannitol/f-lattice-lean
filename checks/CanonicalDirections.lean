import FLatticePaper.Plane.Induction.CanonicalDirections

/-! Checks for task 72 (FIXED_FREE §5 and §6): the canonical first directions and the two cut-tip middles. Each `#guard_msgs` fails unless the axioms are as stated. -/
/--
info: 'FLatticePaper.Induction.CanonicalDirections.prescribedH_hLast_sub_U' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.CanonicalDirections.prescribedH_hLast_sub_U

/--
info: 'FLatticePaper.Induction.CanonicalDirections.prescribedV_vLast_sub_V' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.CanonicalDirections.prescribedV_vLast_sub_V

/--
info: 'FLatticePaper.Induction.CanonicalDirections.prescribedV_odd_minus_one' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.CanonicalDirections.prescribedV_odd_minus_one

/--
info: 'FLatticePaper.Induction.CanonicalDirections.prescribedV_even_minus_one' does not depend on any axioms
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.CanonicalDirections.prescribedV_even_minus_one

/--
info: 'FLatticePaper.Induction.CanonicalDirections.tip_W0_middle_nonfree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.CanonicalDirections.tip_W0_middle_nonfree

/--
info: 'FLatticePaper.Induction.CanonicalDirections.tip_W1_middle_nonfree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.CanonicalDirections.tip_W1_middle_nonfree
