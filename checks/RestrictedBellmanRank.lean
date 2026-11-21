import FLatticePaper.Plane.RestrictedBellmanRank

open FLatticePaper

/-! Checks for the restricted Bellman rank (task 20): the escape and value bounds, the constrained burning rank from
the absence of restricted forts, and the corollary S3 for the sewn standard field. -/

#print axioms FLatticePaper.restrictedEscapesWithin_succ
#print axioms FLatticePaper.exists_restrictedEscapeDepth
#print axioms FLatticePaper.exists_uniformRestrictedEscapeDepth
#print axioms FLatticePaper.restrictedInputs_add
#print axioms FLatticePaper.restrictedValue_add
#print axioms FLatticePaper.restrictedValue_le_of_uniform_escape
#print axioms FLatticePaper.exists_restrictedValue_fixed
#print axioms FLatticePaper.exists_constrainedBurningRank_of_restrictedNoFort
#print axioms FLatticePaper.starDiff_add_deck
#print axioms FLatticePaper.slipPermits_add_deck
#print axioms FLatticePaper.S3_of_restrictedNoFort
#print axioms FLatticePaper.S3_of_packet_restrictedNoFort
