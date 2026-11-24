import FLatticePaper.Tiles.SeamFinal
import FLatticePaper.Tiles.BottomSeam
import FLatticePaper.Tiles.WalkRows
import FLatticePaper.Tiles.BoundaryWalks

/-! The bottom seam facts at the base words (the first milestone of the copy-level seam).

A walk that is a prefix of a boundary word lies on the boundary of the cell tile: the bottom walk `edgesFrom 0 w₁` is the
first part of `edgesFrom 0 (boundaryWordOf w₁ w₂)`. Hence the bottom and cover facts of a word follow from its standard
boundary word. The base words have their standard boundary words unconditionally (`standardBoundaryWord_of_isBase`), so
`BottomCopyOdd`, `BottomCopyEven`, `CoverNodupOdd`, `CoverNodupEven` hold at every base word. -/

namespace FLatticePaper.Tiles.SeamBase

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.SeamFinal FLatticePaper.Tiles.BottomSeam
open FLatticePaper.Tiles.BoundaryWalks

/-- An edge of the walk along `w₁` is an edge of the boundary of `T`, when `w₁ ++ …` is a boundary word of `T`. -/
theorem mem_boundary_of_prefix {T : CellTile} {c : GInt} {w₁ w₂ : F2Word}
    (h : IsBoundaryFrom T c (boundaryWordOf w₁ w₂)) {e : GInt × GInt} (he : e ∈ edgesFrom c w₁) :
    e ∈ T.boundaryEdges := by
  rw [← h.2.2, List.mem_toFinset]
  have hw : boundaryWordOf w₁ w₂ = w₁ ++ (w₂ ++ ((F2Word.rev w₁).hat ++ (F2Word.rev w₂).hat)) := by
    simp [boundaryWordOf, List.append_assoc]
  rw [hw, edgesFrom_append, List.mem_append]
  exact Or.inl he

/-- The bottom walk of the odd tile of `v` lies on its boundary, when the standard boundary word of the odd tile holds. -/
theorem bottomCopyOdd_of_standardOdd (v : Word) (h : StandardBoundaryOdd v) : BottomCopyOdd v := by
  have hb := ((isBoundaryWordAt_iff _ _ _).1 h).2
  intro e he
  exact mem_boundary_of_prefix hb he

/-- The bottom walk of the even tile of `v` lies on its boundary, when the standard boundary word of the even tile holds. -/
theorem bottomCopyEven_of_standardEven (v : Word) (h : StandardBoundaryEven v) : BottomCopyEven v := by
  have hb := ((isBoundaryWordAt_iff _ _ _).1 h).2
  intro e he
  exact mem_boundary_of_prefix hb he

/-- The four walks of the odd tile of `v` cover its boundary and list it once, when the standard boundary word holds. -/
theorem coverNodupOdd_of_standardOdd (v : Word) (h : StandardBoundaryOdd v) : CoverNodupOdd v := by
  have hb := ((isBoundaryWordAt_iff _ _ _).1 h).2
  refine ⟨fun e he => ?_, hb.2.1⟩
  rw [← hb.2.2] at he
  exact List.mem_toFinset.mp he

/-- The four walks of the even tile of `v` cover its boundary and list it once, when the standard boundary word holds. -/
theorem coverNodupEven_of_standardEven (v : Word) (h : StandardBoundaryEven v) : CoverNodupEven v := by
  have hb := ((isBoundaryWordAt_iff _ _ _).1 h).2
  refine ⟨fun e he => ?_, hb.2.1⟩
  rw [← hb.2.2] at he
  exact List.mem_toFinset.mp he

/-- The bottom seam of the odd tile at a base word. -/
theorem bottomCopyOdd_of_isBase (v : Word) (hb : IsBase v) : BottomCopyOdd v :=
  bottomCopyOdd_of_standardOdd v (standardBoundaryWord_of_isBase v hb).1

/-- The bottom seam of the even tile at a base word. -/
theorem bottomCopyEven_of_isBase (v : Word) (hb : IsBase v) : BottomCopyEven v :=
  bottomCopyEven_of_standardEven v (standardBoundaryWord_of_isBase v hb).2

/-- The cover and nodup facts of the odd tile at a base word. -/
theorem coverNodupOdd_of_isBase (v : Word) (hb : IsBase v) : CoverNodupOdd v :=
  coverNodupOdd_of_standardOdd v (standardBoundaryWord_of_isBase v hb).1

/-- The cover and nodup facts of the even tile at a base word. -/
theorem coverNodupEven_of_isBase (v : Word) (hb : IsBase v) : CoverNodupEven v :=
  coverNodupEven_of_standardEven v (standardBoundaryWord_of_isBase v hb).2

end FLatticePaper.Tiles.SeamBase
