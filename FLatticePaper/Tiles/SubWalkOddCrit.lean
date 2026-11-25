import FLatticePaper.Tiles.SubWalkOdd
import FLatticePaper.Tiles.SubBlockOdd
import FLatticePaper.Tiles.SubCriteria

/-! Task Q25 (sub), the odd bottom walk: the boundary of one block.

A block of the walk starting at the corner `p` is one of the two-letter words `[1,1]` (east, east), `[1,i]` (east, north),
`[i,1]` (north, east). Its edges are boundary edges of a cell tile `T` exactly under the cell criteria of `SubCriteria`
(`east_mem_boundaryEdges_iff`, `north_mem_boundaryEdges_iff`). The membership of a corner in the tile of the odd fraction is
the four-test bound `pB` (`memT_iff`). -/

namespace FLatticePaper.Tiles.SubWalkOddCrit

open FLatticePaper FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.SubBlockOdd FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.CellFourTests

theorem vec_one_eq : Unit4.vec Unit4.one = gOne := rfl

theorem vec_i_eq : Unit4.vec Unit4.i = gI := rfl

/-- A corner `p` is a cell of the tile of the odd fraction iff `pB` holds at its coordinates. -/
theorem memT_iff (f : Fraction) (hodd : (f.num + f.den) % 2 = 1) (hpos : 0 < f.num)
    (hlt : f.num < f.den) (P : Finset GInt) (hP : ∀ z : GInt, z ∈ P ↔ InH f z) (p : GInt) :
    p ∈ cellTileOf P ↔
      pB f.num f.den (max (f.den - 2 * f.num) f.num) (min (f.den - f.num) (3 * f.num - f.den)) p.1 p.2 := by
  rw [SubCriteria.mem_cellTileOf_iff]
  rcases p with ⟨x, y⟩
  exact cell_iff_pB f hodd hpos hlt P hP x y

/-- The block `[1,1]` at `p`: two east steps, both boundary edges. -/
theorem bd_EE (T : CellTile) (p : GInt)
    (h1 : p ∈ T) (h2 : p - gI ∉ T) (h3 : p + gOne ∈ T) (h4 : p + gOne - gI ∉ T) :
    ∀ e ∈ edgesFrom p [Unit4.one, Unit4.one], e ∈ T.boundaryEdges := by
  intro e he
  simp only [edgesFrom, vec_one_eq, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact (SubCriteria.east_mem_boundaryEdges_iff T p).2 ⟨h1, h2⟩
  · exact (SubCriteria.east_mem_boundaryEdges_iff T (p + gOne)).2 ⟨h3, h4⟩

/-- The block `[1,i]` at `p`: an east step and then a north step. -/
theorem bd_EN (T : CellTile) (p : GInt)
    (h1 : p ∈ T) (h2 : p - gI ∉ T) (h3 : p + gOne ∉ T) :
    ∀ e ∈ edgesFrom p [Unit4.one, Unit4.i], e ∈ T.boundaryEdges := by
  intro e he
  simp only [edgesFrom, vec_one_eq, vec_i_eq, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact (SubCriteria.east_mem_boundaryEdges_iff T p).2 ⟨h1, h2⟩
  · refine (SubCriteria.north_mem_boundaryEdges_iff T (p + gOne)).2 ⟨?_, h3⟩
    rw [add_sub_cancel_right]
    exact h1

/-- The block `[i,1]` at `p`: a north step and then an east step. -/
theorem bd_NE (T : CellTile) (p : GInt)
    (h1 : p - gOne ∈ T) (h2 : p ∉ T) (h3 : p + gI ∈ T) :
    ∀ e ∈ edgesFrom p [Unit4.i, Unit4.one], e ∈ T.boundaryEdges := by
  intro e he
  simp only [edgesFrom, vec_one_eq, vec_i_eq, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl
  · exact (SubCriteria.north_mem_boundaryEdges_iff T p).2 ⟨h1, h2⟩
  · refine (SubCriteria.east_mem_boundaryEdges_iff T (p + gI)).2 ⟨h3, ?_⟩
    rw [add_sub_cancel_right]
    exact h2

end FLatticePaper.Tiles.SubWalkOddCrit
