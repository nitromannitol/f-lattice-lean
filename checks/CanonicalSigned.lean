import FLatticePaper.CanonicalHeadline

/-! Checks for task 71: the producing direction from the canonical signed policy to `OldPolicyData`, and the headline restated with
`CanonicalSignedPolicy` at proper words. Each `#guard_msgs` fails unless the axioms are exactly the standard three. -/
/--
info: 'FLatticePaper.Induction.laplacian_eq_zero_of_unseeded_forced' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.laplacian_eq_zero_of_unseeded_forced

/--
info: 'FLatticePaper.Induction.forcedRetained_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.forcedRetained_of_canonical

/--
info: 'FLatticePaper.Induction.price_nonincreasing_of_canonical' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.price_nonincreasing_of_canonical

/--
info: 'FLatticePaper.Induction.rawSlip_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.rawSlip_of_canonical

/--
info: 'FLatticePaper.Induction.oldPolicyData_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.oldPolicyData_of_canonical

/--
info: 'FLatticePaper.odometersTheorem_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.odometersTheorem_of_canonical

/--
info: 'FLatticePaper.Induction.translated_rawSlip' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.translated_rawSlip

/--
info: 'FLatticePaper.Induction.rawSlipMinus_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.rawSlipMinus_of_canonical
