import FLatticePaper.Plane.RestrictedBellmanRank
import FLatticePaper.MainTheorems

open FLatticePaper

/-! Checks for task 30: the S3 restricted no-fort premise restated with the grade `cutGrade F 1 1 1`. -/

#print axioms FLatticePaper.Induction.ChildFrame.cutGrade_kernel_zsmul
#print axioms FLatticePaper.Induction.ChildFrame.cutGrade_transverse_zsmul
#print axioms FLatticePaper.Induction.ChildFrame.cutGrade_add_combine
#print axioms FLatticePaper.S3_of_restrictedNoFort
#print axioms FLatticePaper.S3_of_packet_restrictedNoFort
#print axioms FLatticePaper.starEstimates_of_localPremises

/-! Checks for task 30, I3A: the grade `i3aGrade` (the conjugate cut grade with η = ε, transported by the quarter turn). -/
#print axioms FLatticePaper.Induction.i3aGrade_deck
#print axioms FLatticePaper.Induction.localPremises_of_variant
#print axioms FLatticePaper.Induction.packet_of_localPremises'
#print axioms FLatticePaper.odometersTheorem_of_localPremises'
