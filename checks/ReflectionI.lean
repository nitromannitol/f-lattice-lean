import FLatticePaper.CanonicalHeadline

/-! Checks for task 72 (b): the reflection about `I` of the clause system (`ReflectionI.lean`), the restricted `OldPolicyData.reflection`
at black and forced roots, and the black-root facts used by `nonfree_drop_excluded`. Each `#guard_msgs` fails unless the axioms are
exactly the standard three (or a subset of them). -/
/--
info: 'FLatticePaper.Induction.forced_reflectI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.forced_reflectI

/--
info: 'FLatticePaper.Induction.laplacian_reflectI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.laplacian_reflectI

/--
info: 'FLatticePaper.Induction.edge_reflectI' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.edge_reflectI

/--
info: 'FLatticePaper.Induction.reflection_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.reflection_of_canonical

/--
info: 'FLatticePaper.Induction.blackRoot_of_black' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.blackRoot_of_black

/--
info: 'FLatticePaper.Induction.blackRoot_of_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.blackRoot_of_nonneg

/--
info: 'FLatticePaper.Induction.nonfree_drop_excluded' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.nonfree_drop_excluded

/--
info: 'FLatticePaper.odometersTheorem_of_canonical' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.odometersTheorem_of_canonical
