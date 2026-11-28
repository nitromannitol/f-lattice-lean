import FLatticePaper.Tiles.StackedColumnFacts
import FLatticePaper.Tiles.StackedTopLink

/-! The column facts of the even standard tile, mirroring the odd ones (`StackedColumnFacts.odd_column_iff`,
`StackedBottomLink.odd_lower_link`, `StackedTopLink.odd_upper_link`). The quarter turn of `evenTile w` is a translate of the odd
standard tile of the swapped word (`rot_standard_tiles`, second component), so the columns of the even tile are the rows of the
odd tile of the swapped word. The lower and upper bounds of the sites over a column come from the bottom walk `evenBottom w` and
its reflection through `halfTurnCentre (evenTile w)`; the half-turn invariance of the even tile is `MarksIn.halfTurn_evenTile`. -/

namespace FLatticePaper.Tiles.StackedEvenColumns

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.BoundaryTransport FLatticePaper.Tiles.StackedBottomLink FLatticePaper.Tiles.StackedColumnFacts

/-- **The column form of the even standard tile.** The quarter turn of `evenTile w` is a translate `shift (oddTile (swapW w)) a`,
so the columns of the even tile are the rows of the odd tile of the swapped word. -/
theorem even_column_iff (w : Word) (a : GInt) (hrot : rot (evenTile w) = shift (oddTile (swapW w)) a) (t y : ℤ) :
    ((t, y) : GInt) ∈ cellTileOf (evenTile w) ↔
      (0 ≤ t - a.2 ∧ t - a.2 < cntI (oddBottom (swapW w)) + cntI (oddRight (swapW w))) ∧
        Srow (0, 0) (oddBottom (swapW w)) (oddRight (swapW w)) (t - a.2) ≤ -y - 1 - a.1 ∧
        -y - 1 - a.1 < Nrow (0, 0) (oddBottom (swapW w)) (oddRight (swapW w)) (t - a.2) :=
  column_iff_row (OverlapSides.boundary_odd (swapW w)) (StandardBoundary.admissible_oddStandard (swapW w)).1.1
    (OverlapSides.letters_w2 (StandardBoundary.admissible_oddStandard (swapW w)).2) (evenTile w) a hrot t y

/-- **The lower bound of the sites of the even standard tile over a column**, by its bottom walk `evenBottom w`. -/
theorem even_lower_link (w : Word) (x : GInt) (hx : x ∈ evenTile w) (t : ℤ) (ht : x.1 = t) (ht0 : 0 ≤ t)
    (htF : t ≤ (F2Word.sum (evenBottom w)).1) :
    ∃ h : ℤ, h ≤ x.2 ∧ ((t, h) : GInt) ∈ F2Word.walk (0, 0) (evenBottom w) :=
  lower_link (evenTile w) (evenBottom w) (evenRight w) (evenTile_hcc w) (OverlapSides.boundary_even w)
    (StandardBoundary.admissible_evenStandard w).1.1 (OverlapSides.letters_w2 (StandardBoundary.admissible_evenStandard w).2)
    x hx t ht ht0 htF

/-- **The upper bound of the sites of the even standard tile over a column**, by the bottom walk `evenBottom w` reflected through
`halfTurnCentre (evenTile w)`. -/
theorem even_upper_link (w : Word) (x : GInt) (hx : x ∈ evenTile w) (t : ℤ) (ht : x.1 = t)
    (hlo : 0 ≤ (halfTurnCentre (evenTile w)).1 - t)
    (hhi : (halfTurnCentre (evenTile w)).1 - t ≤ (F2Word.sum (evenBottom w)).1) :
    ∃ h : ℤ, x.2 ≤ h ∧ ∃ p ∈ F2Word.walk (0, 0) (evenBottom w),
      halfTurnCentre (evenTile w) - p = ((t, h) : GInt) := by
  have hx' : halfTurn (evenTile w) x ∈ evenTile w := MarksIn.halfTurn_evenTile w x hx
  have hfst : (halfTurn (evenTile w) x).1 = (halfTurnCentre (evenTile w)).1 - t := by
    show (halfTurnCentre (evenTile w)).1 - x.1 = _
    rw [ht]
  have hsnd : (halfTurn (evenTile w) x).2 = (halfTurnCentre (evenTile w)).2 - x.2 := rfl
  obtain ⟨h', hh', hw⟩ :=
    even_lower_link w (halfTurn (evenTile w) x) hx' ((halfTurnCentre (evenTile w)).1 - t) hfst hlo hhi
  refine ⟨(halfTurnCentre (evenTile w)).2 - h', ?_, ((halfTurnCentre (evenTile w)).1 - t, h'), hw, ?_⟩
  · rw [hsnd] at hh'
    omega
  · ext <;> simp

end FLatticePaper.Tiles.StackedEvenColumns
