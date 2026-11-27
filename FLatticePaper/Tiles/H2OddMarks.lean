import FLatticePaper.Tiles.VertexEdge
import FLatticePaper.Tiles.WalkDecomp
import FLatticePaper.Tiles.HorizontalPair
import FLatticePaper.Tiles.VerticalH2
import FLatticePaper.Tiles.VerticalRevBridge
import FLatticePaper.Tiles.OverlapSides
import FLatticePaper.Tiles.SiteLowLeft
import FLatticePaper.Tiles.SiteInduction

/-! The H2 hypothesis `H2o` of the odd standard tile, as a boundary-vertex statement: a boundary vertex of the cell region of
`oddTile w` lies in `marksOdd w`.

A boundary vertex lies on the boundary walk of the tile (`VertexEdge.mem_walk_of_boundaryVertex`). The walk is the four sides
(`WalkDecomp.walk_decomp`), and each side lies in the marks:
* the bottom side in the horizontal string sites (`HBottom.hB_odd`);
* the top side in the marks (`HorizontalPair.top_marks_odd_all`);
* the left side in the vertical marks, since the reversed vertical string covers its translate (`VerticalH2.S4_odd_all`) and
  the cover is the marked vertical sites (`VerticalRevBridge.mem_marked_vert_iff`);
* the right side as the half-turn of the left side, since right = `Σ w1 + t` and left = `Σ w2 - t` have sum `halfTurnCentre`. -/

namespace FLatticePaper.Tiles.H2OddMarks

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
  FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.Standard FLatticePaper.Tiles.CellDerivation

/-- The left side of the odd tile lies in the vertical cover: a point of the reflected walk of the vertical word is in `Mv` of the
reversed vertical word from `0`. -/
theorem odd_Mv_of_left (w : Word) (p : GInt)
    (hp : p ∈ (F2Word.walk 0 (oddRight w)).map (fun y => F2Word.sum (oddRight w) - y)) :
    p ∈ VerticalRevBridge.Mv (vWordOf w false).reverse 0 := by
  have h := (VerticalRevBridge.covers_iff_Mv (vWordOf w false).reverse (texV1Odd (fracOdd w))
    (p + texV1Odd (fracOdd w))).1 (VerticalH2.S4_odd_all w p hp)
  simpa using h

/-- The vertical marked sites of a point of `Mv`. -/
theorem mem_Sv_of_Mv (u : BinaryWord) (z : GInt) (h : z ∈ VerticalRevBridge.Mv u 0) :
    z ∈ (stringSites true true u).map (fun s => (s.1 + ((0 : GInt).1) - 1, s.2 + ((0 : GInt).2) - 1)) :=
  (VerticalRevBridge.mem_marked_vert_iff u z).2 ((VerticalRevBridge.covers_iff_Mv u (0, 0) z).2
    (by rw [show z - ((0, 0) : GInt) = z from by ext <;> simp]; exact h))

theorem mem_marks_bottom_odd (w : Word) (z : GInt) (h : z ∈ stringSites false false (hWordOf w false)) :
    z ∈ markedSites (oddTile w) (hWordOf w false) (vWordOf w false) := by
  have hc : z ∈ (stringSites false false (hWordOf w false)).map
      (fun s => (s.1 + ((0 : GInt).1), s.2 + ((0 : GInt).2))) :=
    List.mem_map.2 ⟨z, h, by simp⟩
  unfold markedSites
  simp only [FLatticePaper.Tiles.SiteLowLeft.lowLeft_oddTile]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hc))

theorem mem_marks_left_odd (w : Word) (z : GInt) (h : z ∈ VerticalRevBridge.Mv (vWordOf w false).reverse 0) :
    z ∈ markedSites (oddTile w) (hWordOf w false) (vWordOf w false) := by
  unfold markedSites
  simp only [FLatticePaper.Tiles.SiteLowLeft.lowLeft_oddTile]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (mem_Sv_of_Mv _ z h)))

theorem mem_marks_right_odd (w : Word) (z p : GInt) (hpM : p ∈ VerticalRevBridge.Mv (vWordOf w false).reverse 0)
    (hz : halfTurn (oddTile w) p = z) :
    z ∈ markedSites (oddTile w) (hWordOf w false) (vWordOf w false) := by
  unfold markedSites
  simp only [FLatticePaper.Tiles.SiteLowLeft.lowLeft_oddTile]
  exact List.mem_append_right _ (List.mem_map.2 ⟨p, mem_Sv_of_Mv _ p hpM, hz⟩)

theorem halfTurn_odd_eq (w : Word) (z t p : GInt) (hz : z = (0 + F2Word.sum (oddBottom w)) + t)
    (hp : p = F2Word.sum (oddRight w) - t) : halfTurn (oddTile w) p = z := by
  rw [show halfTurn (oddTile w) p = halfTurnCentre (oddTile w) - p from rfl, ← HorizontalPair.hP_odd w, hp, hz]
  abel

/-- **H2o for the odd child, the walk form.** A boundary vertex of the cell region of the odd tile of `w` lies in its marks. -/
theorem H2o_odd_full (w : Word) :
    ∀ z, BoundaryVertex (↑(cellTileOf (oddTile w)) : Set GInt) z → z ∈ marksOdd w := by
  intro z hz
  show z ∈ markedSites (oddTile w) (hWordOf w false) (vWordOf w false)
  have hw := VertexEdge.mem_walk_of_boundaryVertex _ (0, 0) _ (OverlapSides.boundary_odd w) z hz
  rw [Prod.mk_zero_zero] at hw
  have hp : boundaryWordOf (oddBottom w) (oddRight w) = pseudoBoundaryWord (oddBottom w) (oddRight w) := rfl
  rw [hp, WalkDecomp.walk_decomp] at hw
  simp only [List.mem_append] at hw
  rcases hw with ((hA | hB) | hC) | hD
  · exact mem_marks_bottom_odd w z (HBottom.hB_odd w z hA)
  · obtain ⟨t, ht, hzt⟩ := List.mem_map.1 (by
      rw [WalkDecomp.walk_translate] at hB
      exact List.mem_of_mem_tail hB)
    have hp' : F2Word.sum (oddRight w) - t ∈
        (F2Word.walk 0 (oddRight w)).map (fun y => F2Word.sum (oddRight w) - y) :=
      List.mem_map.2 ⟨t, ht, rfl⟩
    exact mem_marks_right_odd w z _ (odd_Mv_of_left w _ hp') (halfTurn_odd_eq w z t _ hzt.symm rfl)
  · exact HorizontalPair.top_marks_odd_all w z (List.mem_of_mem_tail hC)
  · obtain ⟨y, hy, hyz⟩ := List.mem_map.1 (List.mem_of_mem_tail hD)
    have hmem : z ∈ (F2Word.walk 0 (oddRight w)).map (fun y => F2Word.sum (oddRight w) - y) :=
      List.mem_map.2 ⟨y, hy, by rw [← hyz]; simp⟩
    exact mem_marks_left_odd w z (odd_Mv_of_left w z hmem)

end FLatticePaper.Tiles.H2OddMarks
