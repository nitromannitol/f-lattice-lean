import FLatticePaper.Tiles.StandardBoundary

/-! Task 54, numerical check (not part of the build's theorems): the recursion words of the standard tiles, for all words
of length 0..6, printed for comparison with the arcs of the actual tiles traced from (0,0). -/

namespace SeamWordsCheck

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.StandardBoundary

def showU : Unit4 → String
  | .one => "1"
  | .i => "i"
  | .negOne => "-1"
  | .negI => "-i"

def showW (w : F2Word) : String := String.intercalate "," (w.map showU)

def showD : Digit → String
  | .one => "1"
  | .two => "2"
  | .three => "3"

def wordsLen : ℕ → List Word
  | 0 => [[]]
  | n + 1 => (wordsLen n).flatMap (fun w => [w ++ [Digit.one], w ++ [Digit.two], w ++ [Digit.three]])

def line (w : Word) : String :=
  "W " ++ String.intercalate "" (w.map showD) ++
    " | OB " ++ showW (oddBottom w) ++ " | OR " ++ showW (oddRight w) ++
    " | EB " ++ showW (evenBottom w) ++ " | ER " ++ showW (evenRight w)

#eval IO.println (String.intercalate "\n" ((List.range 7).flatMap (fun n => (wordsLen n).map line)))

end SeamWordsCheck
