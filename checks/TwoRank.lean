import FLatticePaper.Plane.Induction.TwoRank

/-! Checks for task 72 / Q20 (the two-rank local step): the axioms are as stated. -/
/--
info: 'FLatticePaper.TwoRank.local_two_rank' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.TwoRank.local_two_rank

/--
info: 'FLatticePaper.TwoRank.rise_local_frame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.TwoRank.rise_local_frame

/--
info: 'FLatticePaper.TwoRank.laplacian_translate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.TwoRank.laplacian_translate

/--
info: 'FLatticePaper.TwoRank.incomingNeg_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.TwoRank.incomingNeg_add

/--
info: 'FLatticePaper.TwoRank.add_neg_smul_cancel' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.TwoRank.add_neg_smul_cancel

