import FLatticePaper.Plane.Induction.NegChart

/-! Checks for task 69 (a)/(b): the A-case for `−σ`. Standard axioms only. The leaves that remain are the endpoint range
`hA01` (the price range of `a` on `E`) and the tie leaf `hTie`; the monotonicity of the raw slip and the unit increments are
derived (`hbmono_of_raw`, `a_unit_bound`). -/
#print axioms FLatticePaper.Induction.sheetB_eq
#print axioms FLatticePaper.Induction.hbmono_of_raw
#print axioms FLatticePaper.Induction.a_unit_bound
#print axioms FLatticePaper.Induction.reflect_edge_even
#print axioms FLatticePaper.Induction.ChildFrame.F_sub_shortShift
#print axioms FLatticePaper.Induction.ChildFrame.rising_reflect_neg
#print axioms FLatticePaper.Induction.sheetPolicyA_of_black
#print axioms FLatticePaper.Induction.neg_chart_arith
#print axioms FLatticePaper.Induction.neg_first_excluded
#print axioms FLatticePaper.Induction.neg_adjacent_excluded
#print axioms FLatticePaper.Induction.neg_sign_excluded
#print axioms FLatticePaper.Induction.noBlackPairRise_of_leaves
