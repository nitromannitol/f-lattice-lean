import FLatticePaper.CanonicalHeadline

/-! Checks for task 72 (nonfree root, deck form): the Laplacian is invariant under the child deck, unseeded forced edges are carried by
such translations, and a nonfree root of the old policy is black or has its retained edge forced. Each `#guard_msgs` fails unless the
axioms are standard. -/
/--
info: 'FLatticePaper.Induction.laplacian_span_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.laplacian_span_inv

/--
info: 'FLatticePaper.Induction.forcedEdge_add' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.forcedEdge_add

/--
info: 'FLatticePaper.Induction.nonfree_root_forced_nonfree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.nonfree_root_forced_nonfree

/--
info: 'FLatticePaper.Induction.span_pred' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms FLatticePaper.Induction.span_pred
