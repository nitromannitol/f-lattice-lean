import FLatticePaper.Tiles.StackedBottomLink
import FLatticePaper.Tiles.MarksIn

/-! The upper bound of the sites of the odd standard tile over a column, by its top side. The standard tile is invariant under its
half-turn (`MarksIn.halfTurn_oddTile`), so the top side of the tile is the bottom walk reflected through `halfTurnCentre`. A site
`x` over a column `t` is reflected to a site `halfTurn x` over the column `halfTurnCentre.1 - t`, and the lower bound applies there. -/

namespace FLatticePaper.Tiles.StackedTopLink

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StackedBottomLink

/-- **The upper bound of the sites over a column.** A site `x` of the odd tile over a column `t` lies at or below a point of the
top side over `t`, which is the bottom walk of `oddBottom w` reflected through `halfTurnCentre (oddTile w)`. -/
theorem odd_upper_link (w : Word) (x : GInt) (hx : x ∈ oddTile w) (t : ℤ) (ht : x.1 = t)
    (hlo : 0 ≤ (halfTurnCentre (oddTile w)).1 - t)
    (hhi : (halfTurnCentre (oddTile w)).1 - t ≤ (F2Word.sum (oddBottom w)).1) :
    ∃ h : ℤ, x.2 ≤ h ∧ ∃ p ∈ F2Word.walk (0, 0) (oddBottom w), halfTurnCentre (oddTile w) - p = ((t, h) : GInt) := by
  have hx' : halfTurn (oddTile w) x ∈ oddTile w := MarksIn.halfTurn_oddTile w x hx
  have hfst : (halfTurn (oddTile w) x).1 = (halfTurnCentre (oddTile w)).1 - t := by
    show (halfTurnCentre (oddTile w)).1 - x.1 = _
    rw [ht]
  have hsnd : (halfTurn (oddTile w) x).2 = (halfTurnCentre (oddTile w)).2 - x.2 := rfl
  obtain ⟨h', hh', hw⟩ := odd_lower_link w (halfTurn (oddTile w) x) hx' ((halfTurnCentre (oddTile w)).1 - t) hfst hlo hhi
  refine ⟨(halfTurnCentre (oddTile w)).2 - h', ?_, ((halfTurnCentre (oddTile w)).1 - t, h'), hw, ?_⟩
  · rw [hsnd] at hh'
    omega
  · ext <;> simp

end FLatticePaper.Tiles.StackedTopLink
