import FLatticePaper.Tiles.SurgicalAltOdometers
import FLatticePaper.Tiles.SiteStrings

/-! # Items (3a) and (3b) of `lemma:alternate_tile_properties` (surgical 571253f, lines 3600-3606)

Item (3) places the first tile of the boundary words of an alternate tile at the lower-left vertex `c(T̂)` (even case, the
word `w_h`) or at `c(T̂) + s` (odd case, the reversed word `rev(w_v)`), with `s` the offset of the odd-first orientation. The two
facts below are the positions of the first tiles of the anchored strings (`hStringAt`, `vRevStringAt`), which is what item (3)
asserts about them. Whether the odd-case anchor of the text is `c(T̂) + s` or the anchor of `def:tile_boundary_strings` is the
question sent to the lead; the lemmas are stated for an arbitrary anchor. -/

namespace FLatticePaper.Tiles

/-- (3a): the first tile of the forward horizontal word, placed at `c`, has lower-left vertex `c`. -/
theorem alt_item3a (wh : BinaryWord) (c : GInt) (hwh : wh ≠ []) :
    ((hStringAt wh c).headD (ZTile.zero, 0)).2 = c := by
  cases wh with
  | nil => exact absurd rfl hwh
  | cons a l =>
    cases l with
    | nil => simp [hStringAt, tileSeq, tileSeqAux, List.scanl_nil]
    | cons b l' => simp [hStringAt, tileSeq, tileSeqAux, List.scanl_cons]

/-- (3b): the first tile of the reversed vertical word, placed at `s`, has lower-left vertex `s`. -/
theorem alt_item3b (u : BinaryWord) (s : GInt) (hu : u ≠ []) :
    ((vRevStringAt u s).headD (ZTile.zero, 0)).2 = s := by
  cases u with
  | nil => exact absurd rfl hu
  | cons a l =>
    cases l with
    | nil => simp [vRevStringAt, List.scanl_nil]
    | cons b l' => simp [vRevStringAt, List.scanl_cons]

end FLatticePaper.Tiles
