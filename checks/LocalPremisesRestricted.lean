import FLatticePaper.MainTheorems

/-! Checks for the restricted-fort variant of the local premises (task 27): the variant implies the original premises,
the packet induction and the odometers theorem run from the variant, and the deck invariance and constrained rank
lemmas used along the way. -/

open FLatticePaper.Induction

#print axioms localPremises_of_variant
#print axioms packet_of_localPremises'
#print axioms constrainedRank_of_variant
#print axioms sheetChainPotential_shift
#print axioms laplacian_fp_add_deck
#print axioms permitA_invariant
#print axioms permitC_invariant
#print axioms FLatticePaper.odometersTheorem_of_localPremises'
