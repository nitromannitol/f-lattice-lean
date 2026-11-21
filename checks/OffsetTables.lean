import FLatticePaper.Construction.OffsetTables

open FLatticePaper.Farey FLatticePaper.Construction

#print axioms FLatticePaper.Construction.standard_odd_phase0
#print axioms FLatticePaper.Construction.standard_odd_phase1
#print axioms FLatticePaper.Construction.standard_even_phase0
#print axioms FLatticePaper.Construction.standard_even_phase1
#print axioms FLatticePaper.Construction.alternate_odd_phase0
#print axioms FLatticePaper.Construction.alternate_odd_phase1
#print axioms FLatticePaper.Construction.alternate_even_phase0
#print axioms FLatticePaper.Construction.alternate_even_phase1
#print axioms FLatticePaper.Construction.seventh_odd_phase0
#print axioms FLatticePaper.Construction.seventh_odd_phase1
#print axioms FLatticePaper.Construction.seventh_even_phase0_one
#print axioms FLatticePaper.Construction.seventh_even_phase0_two
#print axioms FLatticePaper.Construction.seventh_even_phase1_one
#print axioms FLatticePaper.Construction.seventh_even_phase1_two

/-! Numerical checks on the word 11 (W1 even, phase 0) and the word 12 (W1 odd, phase 1). The parents are
(p, q) = (2/5, 3/7) for 11 and (2/5, 1/3) for 12; the values are the translations of the Lean jets. -/

example : (List.range 6).map (fun i => (standardJets [Digit.one, Digit.one] .odd (Fin.ofNat 6 i)).1) =
    [(0, 0), (7, 3), (7, 11), (14, 14), (14, 6), (-4, 10)] := by decide
example : (List.range 6).map (fun i => (standardJets [Digit.one, Digit.one] .even (Fin.ofNat 6 i)).1) =
    [(0, 0), (4, 18), (7, 3), (4, 10), (-4, 10), (-7, 17)] := by decide
example : (List.range 6).map (fun i => (alternateJets [Digit.one, Digit.one] .odd (Fin.ofNat 6 i)).1) =
    [(0, 0), (11, 21), (7, 3), (11, 13), (-4, 10), (0, 20)] := by decide
example : (List.range 6).map (fun i => (alternateJets [Digit.one, Digit.one] .even (Fin.ofNat 6 i)).1) =
    [(0, 0), (-10, 4), (7, 11), (-3, 15), (7, 3), (-14, 14)] := by decide
example : (List.range 6).map (fun i => (standardJets [Digit.one, Digit.two] .odd (Fin.ofNat 6 i)).1) =
    [(10, 4), (13, 5), (-3, 7), (0, 8), (0, 0), (4, 6)] := by decide
example : (List.range 6).map (fun i => (standardJets [Digit.one, Digit.two] .even (Fin.ofNat 6 i)).1) =
    [(10, 4), (-6, 14), (0, 0), (-3, 7), (1, 5), (-2, 12)] := by decide
example : (List.range 6).map (fun i => (alternateJets [Digit.one, Digit.two] .odd (Fin.ofNat 6 i)).1) =
    [(10, 4), (-9, 13), (0, 0), (-6, 6), (1, 5), (-5, 11)] := by decide
example : (List.range 6).map (fun i => (alternateJets [Digit.one, Digit.two] .even (Fin.ofNat 6 i)).1) =
    [(10, 4), (10, 12), (-3, 7), (-3, 15), (0, 0), (1, 13)] := by decide

/-- Agreeing seventh pieces at the word 11 and the word 13. -/
example : (seventhAlternateJet [Digit.one] .one .odd).1 = (4, 10) := by decide
example : (seventhAlternateJet [Digit.one] .one .even).1 = (0, 8) := by decide
example : (seventhAlternateJet [Digit.one] .two .even).1 = (4, 6) := by decide
example : (seventhAlternateJet [Digit.one] .three .odd).1 =
    texV2 (parentsAt [Digit.one, Digit.three]).odd + texV1Odd (parentsAt [Digit.one, Digit.three]).odd -
      texV1Even (parentsAt [Digit.one, Digit.three]).even := by decide

/-! Differing seventh pieces: the paper omits the piece (`−`) for Type 2 with an odd child and Type 3 with an
even child, while the Lean schedule always places it. The values are evaluated, not stated as theorems. -/
#eval (seventhAlternateJet [Digit.one] .two .odd).1
#eval (seventhAlternateJet [Digit.one] .three .even).1
#eval (seventhAlternateJet [Digit.two] .three .even).1
