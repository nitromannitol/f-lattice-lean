import FLatticePaper.Plane.Induction.BaseUpper

open FLatticePaper

/-! Checks for task 36: the pure arc geometry of `E`, the reflection and the lower bound, the upper bound from the
recurrent comparison, and the assembled base range. The hypotheses still open are visible in the statements:
`RecurrentField M` (fort form of the recurrence of the sheet minimum) and `VArcInputs` (the V arcs). -/

#print axioms FLatticePaper.Induction.ChildFrame.pureBottom_strip
#print axioms FLatticePaper.Induction.ChildFrame.pureTop_strip
#print axioms FLatticePaper.Induction.ChildFrame.not_pureBottom_and_pureTop
#print axioms FLatticePaper.Induction.ChildFrame.tGrade_sub_modTransverse
#print axioms FLatticePaper.Induction.onBoundary_cover
#print axioms FLatticePaper.Induction.ChildFrame.starDiff_reflect
#print axioms FLatticePaper.Induction.ChildFrame.exists_representative
#print axioms FLatticePaper.Induction.lower_of_upper
#print axioms FLatticePaper.Induction.closedPolygon_box
#print axioms FLatticePaper.Induction.upper_of_recurrent
#print axioms FLatticePaper.Induction.base_range_of_inputs
