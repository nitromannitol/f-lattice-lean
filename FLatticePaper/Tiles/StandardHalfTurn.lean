import FLatticePaper.Tiles.StandardTiles

/-! The half-turn symmetry of the standard tiles (TeX lemma 2723, step 3).

`rot_standard_tiles` (StandardTiles.lean) turns an odd tile into a translate of the even tile of the swapped word, and
the even tile into a translate of the odd tile. Turning twice is the half-turn, and the swap is an involution, so every
standard tile is half-turn symmetric up to a translation. This is the symmetry that turns the bottom and right boundary
words into the top and left ones (`hat (rev w₁)`, `hat (rev w₂)`). -/

namespace FLatticePaper.Tiles.StandardHalfTurn

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard

theorem swapW_swapW (w : Word) : swapW (swapW w) = w := by
  simp [swapW, List.map_map, Function.comp_def, Digit.swapTwoThree_swapTwoThree]

/-- Turning a translate turns the translation: `rot (shift T v) = shift (rot T) (i·v)`. -/
theorem rot_shift (T : Tile) (v : Site) : rot (shift T v) = shift (rot T) (mulI v) := by
  ext x
  rw [mem_rot, mem_shift, mem_shift, mem_rot]
  have h : ((x.2, -x.1) - v : Site) = ((x - mulI v).2, -(x - mulI v).1) := by
    refine Prod.ext ?_ ?_
    all_goals simp [mulI]
    all_goals ring
  rw [h]

theorem shift_shift (T : Tile) (a b : Site) : shift (shift T a) b = shift T (a + b) := by
  ext x
  rw [mem_shift, mem_shift, mem_shift]
  have h : (x - b - a : Site) = x - (a + b) := by
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  rw [h]

/-- The half-turn of an odd standard tile is a translate of itself. -/
theorem rot_rot_oddTile (w : Word) :
    rot (rot (oddTile w)) =
      shift (oddTile w) (tF ((parentsAt (swapW w)).current .even) + mulI (tF ((parentsAt w).current .odd))) := by
  rw [(rot_standard_tiles w).1, rot_shift, (rot_standard_tiles (swapW w)).2, shift_shift, swapW_swapW]

/-- The half-turn of an even standard tile is a translate of itself. -/
theorem rot_rot_evenTile (w : Word) :
    rot (rot (evenTile w)) =
      shift (evenTile w) (tF ((parentsAt (swapW w)).current .odd) + mulI (tF ((parentsAt w).current .even))) := by
  rw [(rot_standard_tiles w).2, rot_shift, (rot_standard_tiles (swapW w)).1, shift_shift, swapW_swapW]

end FLatticePaper.Tiles.StandardHalfTurn
