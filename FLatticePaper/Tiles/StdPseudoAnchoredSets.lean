import FLatticePaper.Tiles.VerticalRevBridge
import FLatticePaper.Tiles.StringCover
import FLatticePaper.Tiles.ReflectedCover
import FLatticePaper.Tiles.PseudoSquareAnchored

/-! # The placed sets of the anchored strings, as sets of marked sites (first two of the four equalities)

For the E07-anchored predicate `IsPseudoSquareAnchoredPt` on the standard tiles, the placed set of the four strings is compared with
the marked sites of `SiteStrings.markedSites` (at the anchor `c = lowLeft T = (0,0)`). The forward horizontal string and the reversed
vertical string are identified here: the placed set of a tile list is the set of points it covers (`mem_placedSites_iff_tileCovers`),
and the two covers are the existing identifications with `stringSites` (`StringCover.covers_iff_stringSites`,
`VerticalRevBridge.mem_marked_vert_iff`). The two half-turn identities (the reversed horizontal and the forward vertical strings) are
not yet here. -/

namespace FLatticePaper.Tiles.StdPseudoAnchoredSets

open FLatticePaper.Tiles
open FLatticePaper.Tiles.SiteStrings
open FLatticePaper.Tiles.ReflectedCover

/-- A site is placed by a tile list exactly when the list covers it. -/
theorem mem_placedSites_iff_tileCovers : ∀ (ts : List (ZTile × GInt)) (x : GInt),
    x ∈ placedSites ts ↔ tileCovers ts x
  | [], x => by
    simp [placedSites, tileCovers_nil']
  | a :: ts, x => by
    have h := mem_placedSites_iff_tileCovers ts x
    rw [tileCovers_cons']
    simp only [placedSites, List.flatMap_cons, List.mem_append] at h ⊢
    rw [h]

/-- The forward horizontal string at the origin places exactly the marked sites of `w_h` (`stringSites`). -/
theorem placed_hStringAt_iff (h : BinaryWord) (z : GInt) :
    z ∈ placedSites (hStringAt h (0, 0)) ↔ z ∈ stringSites false false h := by
  rw [mem_placedSites_iff_tileCovers]
  exact StringCover.covers_iff_stringSites h z

/-- The reversed vertical string of `u` at the origin places exactly the marked sites of `rev w_v` (shifted by `(-1,-1)`). -/
theorem placed_vRevStringAt_iff (u : BinaryWord) (x : GInt) :
    x ∈ placedSites (vRevStringAt u (0, 0)) ↔
      x ∈ (stringSites true true u).map (fun z => (z.1 + ((0 : GInt).1) - 1, z.2 + ((0 : GInt).2) - 1)) := by
  rw [mem_placedSites_iff_tileCovers, VerticalRevBridge.mem_marked_vert_iff]

end FLatticePaper.Tiles.StdPseudoAnchoredSets
