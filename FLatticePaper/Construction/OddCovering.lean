import FLatticePaper.Construction.PlaneIdentification
import FLatticePaper.Plane.Induction.WordInduction

/-! Task 37, step 1: the odd copy sites are covered by the conjugate lattice.

The odd output target is `planeTarget word .odd = quarterTurnField (standardField (conjWord (word ++ [one])))`, whose
sheets live on the closed polygon `E_s` of the frame of the swapped word `conjWord (word ++ [one]) = word.map swap`. A
site `z` of an odd copy is carried to the quarter-turned site `Z z = (-z.2, z.1 - 1)`; the deck covering of the child
frame (`ChildFrame.closedPolygon_covers`) then places `Z z` as a point of `E_s` plus a combination of the modified deck
of the conjugate child. -/

namespace FLatticePaper.Construction

open FLatticePaper.Induction Farey

/-- The conjugate word of the odd output of `word` is the swapped word `word.map swap`. -/
theorem conjWord_append_one_eq (word : Word) :
    conjWord (word ++ [Digit.one]) = word.map Digit.swapTwoThree := by
  unfold conjWord
  rw [oddBirthPrefix_append_one]

/-- The odd output target is the quarter turn of the standard field of the conjugate word of `word ++ [one]`. -/
theorem planeTarget_odd_eq (word : Word) :
    planeTarget word .odd = quarterTurnField (standardField (conjWord (word ++ [Digit.one]))) := rfl

/-- Step 1 (covering): for every site `z` (in particular every site of an odd copy), its quarter turn `Z z` is a
point of the closed polygon of the swapped word's frame plus a combination of the conjugate child's modified deck. -/
theorem odd_copy_site_covered (word : Word) (z : Site) :
    ∃ y ∈ (frameAt (conjWord (word ++ [Digit.one]))).closedPolygon, ∃ i j : ℤ,
      (-z.2, z.1 - 1) = y +
        (frameAt (conjWord (word ++ [Digit.one]))).child.modifiedDeck.combine i j :=
  (frameAt (conjWord (word ++ [Digit.one]))).closedPolygon_covers (-z.2, z.1 - 1)

/-- The statement for the copy sites of an odd ordinary standard output in any slot. -/
theorem odd_copy_sites_covered (parents : TileParents) (word : Word) (slot : Fin 6)
    (z : Site) (_hz : z ∈ (ordinaryStandardCopy parents word .odd slot).val.sites) :
    ∃ y ∈ (frameAt (conjWord (word ++ [Digit.one]))).closedPolygon, ∃ i j : ℤ,
      (-z.2, z.1 - 1) = y +
        (frameAt (conjWord (word ++ [Digit.one]))).child.modifiedDeck.combine i j :=
  odd_copy_site_covered word z

end FLatticePaper.Construction
