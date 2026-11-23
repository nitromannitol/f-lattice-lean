import FLatticePaper.Plane.Induction.UniformEscape

/-! Checks for task 72 (Q1 paragraphs 7–8): the uniform escape horizon from the finite depths and the deck covariance, and the rank under
the restricted no-fort condition. Each `#guard_msgs` fails unless the axioms are standard. -/
/--
info: 'FLatticePaper.AndOrRank.uniform_escape_horizon' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.AndOrRank.uniform_escape_horizon

/--
info: 'FLatticePaper.AndOrRank.andOr_rank_of_restrictedNoFort' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.AndOrRank.andOr_rank_of_restrictedNoFort
