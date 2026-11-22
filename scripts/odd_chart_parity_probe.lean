import FLatticePaper.Construction.AlternateIdentification

/-! Probe for task 46 (the parity of the odd chart): for every word of length at most four ending in 1 or 3, evaluate the Lean
definition `alternateOddChart` (which includes the restoration of the seventh copy through `alternateOddLowerLeft`) and test
`EvenSite` (the coordinate sum is even). Prints the number of words and the failures. -/

open FLatticePaper.Farey FLatticePaper FLatticePaper.Construction

namespace OddChartParity

def gen : ℕ → List Word
  | 0 => [[]]
  | n + 1 => [Digit.one, Digit.two, Digit.three].flatMap fun d => (gen n).map (d :: ·)

def oddWords : List Word :=
  ((gen 1 ++ gen 2 ++ gen 3 ++ gen 4 ++ gen 5).filter fun w =>
    match w.getLast? with
    | some Digit.one => true
    | some Digit.three => true
    | _ => false)

def fails : List Word := oddWords.filter fun w => !decide (EvenSite (alternateOddChart w))

#eval oddWords.length
#eval fails.length
#eval fails.take 10

end OddChartParity
