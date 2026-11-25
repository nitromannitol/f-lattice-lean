import FLatticePaper.Tiles.SubWalkEven
import FLatticePaper.Tiles.SubCriteria
import FLatticePaper.Tiles.SeamFinal
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.SiteHullEven
import FLatticePaper.Tiles.SiteSourcesAll
import FLatticePaper.Tiles.MarksIn

/-! Task Q25 (sub), the even bottom copy for every word.

`BottomCopyEven v` (the bottom walk of the even child lies on the boundary of its cell tile) is proved for every word, with no named
input: the even tile is the H set of the even current fraction for every word (`evenTile_eq_HSet_all`, from `good_all`), the even
current fraction is in `(0, 1)` with even parity (`curE_pos_lt`, `current_even_parity`), and its ceiling word is the childQ of the quad
(`quadInv_all`). Then `walk_bdE` gives the walk, as `evenBottom v = gH (childQ v)` (`evenBottom_eq_gH`). -/

namespace FLatticePaper.Tiles.SubEvenCopy

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
  FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteHullEven FLatticePaper.Tiles.SubBlockEven
  FLatticePaper.Tiles.SubWalkEven FLatticePaper.Tiles.SeamFinal FLatticePaper.Tiles.CeilWords

/-- The standard even tile is the H set of its even current fraction, for every word. -/
theorem evenTile_eq_HSet_all (w : Word) :
    ((evenTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curE w) :=
  (good_all (FLatticePaper.Tiles.SiteSourcesAll.sourceHyps_of_marks FLatticePaper.Tiles.MarksIn.marks_all) w).2.1

/-- A point is a site of the even tile iff it lies in the H set of the even current fraction. -/
theorem mem_evenTile_iff (w : Word) (z : ℤ × ℤ) : z ∈ evenTile w ↔ InH (curE w) z := by
  have h := Set.ext_iff.1 (evenTile_eq_HSet_all w) z
  rw [Finset.mem_coe] at h
  exact h

/-- The bottom walk of the even child lies on the boundary of its cell tile, for every word. -/
theorem bottomCopyEven_all (v : Word) : BottomCopyEven v := by
  have hpos := curE_pos_lt v
  have hev : ((curE v).num + (curE v).den) % 2 = 0 := (parentsAt_valid v).current_even_parity
  have hP : ∀ z : GInt, z ∈ evenTile v ↔ InH (curE v) z := mem_evenTile_iff v
  have hT : ∀ a b : ℤ, (a, b) ∈ cellTileOf (evenTile v) ↔
      pBE (curE v).num (curE v).den (max ((curE v).den - 2 * (curE v).num) (curE v).num)
        (min ((curE v).den - (curE v).num) (3 * (curE v).num - (curE v).den)) a b :=
    fun a b => (SubCriteria.mem_cellTileOf_iff (evenTile v) (a, b)).trans
      (cell_iff_pBE (curE v) hev hpos.1 hpos.2 (evenTile v) hP a b)
  have hN : 1 ≤ (curE v).num := by omega
  have hC : 1 ≤ (curE v).den - (curE v).num := by omega
  have hM : (curE v).den + (curE v).num = 2 * (((curE v).den + (curE v).num) / 2) := by omega
  have hx : CeilWords.CeilWord (quadAt [] v).childQ (curE v).num (((curE v).den + (curE v).num) / 2) :=
    (CeilWords.quadInv_all v).2.1
  have hw := walk_bdE (curE v).num (curE v).den (((curE v).den + (curE v).num) / 2) hN hC hM
    (quadAt [] v).childQ hx (cellTileOf (evenTile v)) hT
  unfold BottomCopyEven
  intro e he
  rw [show evenBottom v = gH (quadAt [] v).childQ from RegisterLink.evenBottom_eq_gH v] at he
  exact hw e he

end FLatticePaper.Tiles.SubEvenCopy
