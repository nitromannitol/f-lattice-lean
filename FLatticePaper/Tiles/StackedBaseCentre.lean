import FLatticePaper.Tiles.HorizontalPair

/-! The half-turn centre of the odd standard tile in terms of its bottom walk and its second lattice vector: `C = E + v + (1,0)`
with `E = sum (oddBottom w)` the end of the bottom walk and `v = texV2 (fracOdd w)`. This is the base of the top-cell reduction. -/

namespace FLatticePaper.Tiles.StackedBaseCentre

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardBoundary

/-- **The half-turn centre of the odd tile.** `C.1 = E.1 + v.1 + 1` and `C.2 = E.2 + v.2`, where `E = sum (oddBottom w)` and
`v = texV2 (fracOdd w)`. -/
theorem centre_odd_coords (w : Word) :
    (halfTurnCentre (oddTile w)).1 = (F2Word.sum (oddBottom w)).1 + (texV2 (fracOdd w)).1 + 1 ∧
      (halfTurnCentre (oddTile w)).2 = (F2Word.sum (oddBottom w)).2 + (texV2 (fracOdd w)).2 := by
  have h1 := sum_oddBottom w
  have h2 := sum_oddRight w
  have h3 := HorizontalPair.hP_odd w
  unfold almostV₁ at h1
  unfold almostV₂ at h2
  have e1 := congrArg Prod.fst h1
  have e2 := congrArg Prod.snd h1
  have e3 := congrArg Prod.fst h2
  have e4 := congrArg Prod.snd h2
  have e5 := congrArg Prod.fst h3
  have e6 := congrArg Prod.snd h3
  simp only [gI, gOne, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] at e1 e2 e3 e4 e5 e6
  constructor <;> omega

end FLatticePaper.Tiles.StackedBaseCentre
