import FLatticePaper.Farey.RationalBirth
import FLatticePaper.Construction.Chronology

namespace FLatticePaper.Checks

open Farey Construction

private def mixedWord : Word := [.three, .three, .one, .two]

example : (parentsAt mixedWord).current .odd = ⟨3, 20⟩ := by decide

example : (parentsAt mixedWord).current .even = ⟨5, 33⟩ := by decide

example : (splitInitial mixedWord).1.word = [.three, .three] := by decide

example : (splitInitial mixedWord).2 = [.one, .two] := by decide

example : (ancestorHistory mixedWord).readCorrection .two = some [.three, .three, .one] := by
  decide

example : (ancestorHistory mixedWord).readCorrection .three = some mixedWord := by decide

private def mixedBirth : Birth := (mixedWord, .even)

theorem undo_mixedBirth :
    birthOf mixedBirth.fraction mixedBirth.interior mixedBirth.reduced = mixedBirth :=
  mixedBirth.birthOf_fraction mixedBirth.interior mixedBirth.reduced

private def verifyBirths : IO Unit := do
  unless birthOf mixedBirth.fraction mixedBirth.interior mixedBirth.reduced = mixedBirth do
    throw (IO.userError "incorrect inverse word for 5/33")
  unless retainedBirth? mixedWord .odd = some ([.three, .three, .one], .odd) do
    throw (IO.userError "incorrect retained odd birth for 3312")
  unless retainedBirth? mixedWord .even = some ([.three, .three], .even) do
    throw (IO.userError "incorrect retained even birth for 3312")
  IO.println "Mixed words: inverse birth, both retained births, and both saved words checked."

#eval verifyBirths

#print axioms parentsAt_valid
#print axioms Parents.det_walk
#print axioms existsUnique_rational_birth
#print axioms retainedBirth?_eq_some_of_ne_endpoint
#print axioms splitInitial_word
#print axioms ancestorHistory_saved_nonempty
#print axioms undo_mixedBirth

end FLatticePaper.Checks
