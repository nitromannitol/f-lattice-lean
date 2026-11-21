import FLatticePaper.Plane.Induction.StandardField

open FLatticePaper.Induction FLatticePaper.Farey FLatticePaper.Construction

example : (parentsAt []).current .even = ⟨1, 3⟩ := rfl
example : (parentsAt [Digit.three]).current .even = ⟨1, 5⟩ := rfl
example : (parentsAt [Digit.three, Digit.three]).current .even = ⟨1, 7⟩ := rfl

#print axioms FLatticePaper.Induction.ChildFrame.sewnField_spec
#print axioms FLatticePaper.Induction.standardField_threes
#print axioms FLatticePaper.Induction.standardField_proper
#print axioms FLatticePaper.Induction.parentsAt_odd_eq
#print axioms FLatticePaper.Induction.oddBirthPrefix_length_lt
#print axioms FLatticePaper.Induction.all_three_eq_replicate
