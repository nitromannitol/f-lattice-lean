import FLatticePaper.Tiles.VertexEdge
import FLatticePaper.Tiles.WalkDecomp
import FLatticePaper.Tiles.HorizontalPair
import FLatticePaper.Tiles.HBottom
import FLatticePaper.Tiles.VerticalH2
import FLatticePaper.Tiles.VerticalRevBridge
import FLatticePaper.Tiles.OverlapSides
import FLatticePaper.Tiles.SiteLowLeft
import FLatticePaper.Tiles.SiteInduction
import FLatticePaper.Tiles.H2OddMarks

/-! The H2 hypothesis of the even standard tile, as a boundary-vertex statement: a boundary vertex of the cell region of
`evenTile w` lies in `marksEven w`. This is the even analogue of `H2OddMarks.H2o_odd_full`, with the same four sides of the
boundary walk: the bottom side (`HBottom.hB_even`), the top side (`HorizontalPair.top_marks_even`), the left side through the
reversed vertical cover (`VerticalH2.S4_even_all`) and the right side as the half-turn of the left side (`HorizontalPair.hP_even`).
The vertical marked sites `H2OddMarks.mem_Sv_of_Mv` are generic in the word. -/

namespace FLatticePaper.Tiles.H2EvenMarks

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
  FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SiteStrings
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.Standard FLatticePaper.Tiles.CellDerivation

/-- The left side of the even tile lies in the vertical cover: a point of the reflected walk of the even vertical word is in `Mv`
of the reversed vertical word from `0`. -/
theorem even_Mv_of_left (w : Word) (p : GInt)
    (hp : p ∈ (F2Word.walk 0 (evenRight w)).map (fun y => F2Word.sum (evenRight w) - y)) :
    p ∈ VerticalRevBridge.Mv (vWordOf w true).reverse 0 := by
  have h := (VerticalRevBridge.covers_iff_Mv (vWordOf w true).reverse (texV1Even (fracEven w))
    (p + texV1Even (fracEven w))).1 (VerticalH2.S4_even_all w p hp)
  simpa using h

theorem mem_marks_bottom_even (w : Word) (z : GInt) (h : z ∈ stringSites false false (hWordOf w true)) :
    z ∈ markedSites (evenTile w) (hWordOf w true) (vWordOf w true) := by
  have hc : z ∈ (stringSites false false (hWordOf w true)).map
      (fun s => (s.1 + ((0 : GInt).1), s.2 + ((0 : GInt).2))) :=
    List.mem_map.2 ⟨z, h, by simp⟩
  unfold markedSites
  simp only [FLatticePaper.Tiles.SiteLowLeft.lowLeft_evenTile]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hc))

theorem mem_marks_left_even (w : Word) (z : GInt) (h : z ∈ VerticalRevBridge.Mv (vWordOf w true).reverse 0) :
    z ∈ markedSites (evenTile w) (hWordOf w true) (vWordOf w true) := by
  unfold markedSites
  simp only [FLatticePaper.Tiles.SiteLowLeft.lowLeft_evenTile]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (H2OddMarks.mem_Sv_of_Mv _ z h)))

theorem mem_marks_right_even (w : Word) (z p : GInt) (hpM : p ∈ VerticalRevBridge.Mv (vWordOf w true).reverse 0)
    (hz : halfTurn (evenTile w) p = z) :
    z ∈ markedSites (evenTile w) (hWordOf w true) (vWordOf w true) := by
  unfold markedSites
  simp only [FLatticePaper.Tiles.SiteLowLeft.lowLeft_evenTile]
  exact List.mem_append_right _ (List.mem_map.2 ⟨p, H2OddMarks.mem_Sv_of_Mv _ p hpM, hz⟩)

theorem halfTurn_even_eq (w : Word) (z t p : GInt) (hz : z = (0 + F2Word.sum (evenBottom w)) + t)
    (hp : p = F2Word.sum (evenRight w) - t) : halfTurn (evenTile w) p = z := by
  rw [show halfTurn (evenTile w) p = halfTurnCentre (evenTile w) - p from rfl, ← HorizontalPair.hP_even w, hp, hz]
  abel

/-- **H2e for the even child, the walk form.** A boundary vertex of the cell region of the even tile of `w` lies in its marks. -/
theorem H2e_even_full (w : Word) :
    ∀ z, BoundaryVertex (↑(cellTileOf (evenTile w)) : Set GInt) z → z ∈ marksEven w := by
  intro z hz
  show z ∈ markedSites (evenTile w) (hWordOf w true) (vWordOf w true)
  have hw := VertexEdge.mem_walk_of_boundaryVertex _ (0, 0) _ (OverlapSides.boundary_even w) z hz
  rw [Prod.mk_zero_zero] at hw
  have hp : boundaryWordOf (evenBottom w) (evenRight w) = pseudoBoundaryWord (evenBottom w) (evenRight w) := rfl
  rw [hp, WalkDecomp.walk_decomp] at hw
  simp only [List.mem_append] at hw
  rcases hw with ((hA | hB) | hC) | hD
  · exact mem_marks_bottom_even w z (HBottom.hB_even w z hA)
  · have h1 := List.mem_of_mem_tail hB
    rw [WalkDecomp.walk_translate] at h1
    obtain ⟨t, ht, hzt⟩ := List.mem_map.1 h1
    have hp' : F2Word.sum (evenRight w) - t ∈
        (F2Word.walk 0 (evenRight w)).map (fun y => F2Word.sum (evenRight w) - y) :=
      List.mem_map.2 ⟨t, ht, rfl⟩
    exact mem_marks_right_even w z _ (even_Mv_of_left w _ hp') (halfTurn_even_eq w z t _ hzt.symm rfl)
  · exact HorizontalPair.top_marks_even w z (List.mem_of_mem_tail hC)
  · obtain ⟨y, hy, hyz⟩ := List.mem_map.1 (List.mem_of_mem_tail hD)
    have hmem : z ∈ (F2Word.walk 0 (evenRight w)).map (fun y => F2Word.sum (evenRight w) - y) :=
      List.mem_map.2 ⟨y, hy, by rw [← hyz]; simp⟩
    exact mem_marks_left_even w z (even_Mv_of_left w z hmem)

end FLatticePaper.Tiles.H2EvenMarks
