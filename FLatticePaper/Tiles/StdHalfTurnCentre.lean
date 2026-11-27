import FLatticePaper.Tiles.SiteHullEven
import FLatticePaper.Tiles.StandardClauseA

/-! # The half-turn centre of the standard tiles, in the offsets of the string identities

The half-turn centre of the odd standard tile of `w` is `X + Y + (1,-1)` with `X = texV1Odd (fracOdd w)` and
`Y = texV2 (fracOdd w)`, and likewise for the even tile with `texV1Even`, `fracEven`. These are the constants of the
reflected strings: the reversed horizontal string anchored at `Y + (1,-2)` is the half-turn of the forward one about `X + Y + (1,-1)`,
and the forward vertical string anchored at `X - (1,1)` is the half-turn of the reversed one about `X + Y + (1,-1)`. -/

namespace FLatticePaper.Tiles.StdHalfTurnCentre

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.SiteStrings FLatticePaper.Tiles.Standard

theorem stdCentre_odd (w : Word) :
    halfTurnCentre (oddTile w) = texV1Odd (fracOdd w) + texV2 (fracOdd w) + (1, -1) := by
  rw [SiteHullOdd.centre_odd]
  unfold texV1Odd texV2 fracOdd
  ext
  all_goals simp
  all_goals ring

theorem stdCentre_even (w : Word) :
    halfTurnCentre (evenTile w) = texV1Even (fracEven w) + texV2 (fracEven w) + (1, -1) := by
  rw [SiteHullEven.centre_even]
  unfold texV1Even texV2 fracEven
  ext
  all_goals simp
  all_goals ring

end FLatticePaper.Tiles.StdHalfTurnCentre
