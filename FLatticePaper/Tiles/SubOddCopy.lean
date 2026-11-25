import FLatticePaper.Tiles.SubWalkOddBound
import FLatticePaper.Tiles.SubWalkOddCrit
import FLatticePaper.Tiles.SeamFinal
import FLatticePaper.Tiles.RegisterLink
import FLatticePaper.Tiles.SiteHullOdd
import FLatticePaper.Tiles.SiteSourcesAll
import FLatticePaper.Tiles.MarksIn

/-! Task Q25 (sub), the odd bottom copy for every word.

`BottomCopyOdd v` (the bottom walk of the odd child lies on the boundary of its cell tile) is proved for every word, with no named
input: the odd tile is the H set of the odd current fraction for every word (`oddTile_eq_HSet_all`, from the marks of every
standard tile, `marks_all`), the current odd fraction is in `(0, 1)` with odd parity (`curO_pos_lt`, `curO_odd`), and its ceiling
word is the childP of the quad (`quadInv_all`). Then `walk_bd` gives the walk. -/

namespace FLatticePaper.Tiles.SubOddCopy

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
  FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause
  FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteHullOdd FLatticePaper.Tiles.SubBlockOdd
  FLatticePaper.Tiles.SubWalkOddCrit FLatticePaper.Tiles.SubWalkOddBound FLatticePaper.Tiles.SeamFinal

/-- The standard odd tile is the H set of its odd current fraction, for every word. -/
theorem oddTile_eq_HSet_all (w : Word) :
    ((oddTile w : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet (curO w) :=
  (good_all (FLatticePaper.Tiles.SiteSourcesAll.sourceHyps_of_marks FLatticePaper.Tiles.MarksIn.marks_all) w).1

/-- A point is a site of the odd tile iff it lies in the H set of the odd current fraction. -/
theorem mem_oddTile_iff (w : Word) (z : ℤ × ℤ) : z ∈ oddTile w ↔ InH (curO w) z := by
  have h := Set.ext_iff.1 (oddTile_eq_HSet_all w) z
  rw [Finset.mem_coe] at h
  exact h

/-- The bottom walk of the odd child lies on the boundary of its cell tile, for every word. -/
theorem bottomCopyOdd_all (v : Word) : BottomCopyOdd v := by
  have hcur := curO_pos_lt v
  have hodd : ((curO v).num + (curO v).den) % 2 = 1 := curO_odd v
  have hP : ∀ z : GInt, z ∈ oddTile v ↔ InH (curO v) z := mem_oddTile_iff v
  have hT : ∀ a b : ℤ, (a, b) ∈ cellTileOf (oddTile v) ↔
      pB (curO v).num (curO v).den (max ((curO v).den - 2 * (curO v).num) (curO v).num)
        (min ((curO v).den - (curO v).num) (3 * (curO v).num - (curO v).den)) a b :=
    fun a b => SubWalkOddCrit.memT_iff (curO v) hodd hcur.1 hcur.2 (oddTile v) hP (a, b)
  have hx : CeilWords.CeilWord (quadAt [] v).childP (2 * (curO v).num) ((curO v).den + (curO v).num) :=
    (CeilWords.quadInv_all v).1
  have hN : 1 ≤ (curO v).num := by omega
  have hC : 1 ≤ (curO v).den - (curO v).num := by omega
  have hw := SubWalkOddBound.walk_bd (curO v).num (curO v).den hN hC (quadAt [] v).childP hx
    (cellTileOf (oddTile v)) hT
  unfold BottomCopyOdd
  intro e he
  rw [show oddBottom v = gH (quadAt [] v).childP from RegisterLink.oddBottom_eq_gH v] at he
  exact hw e he

end FLatticePaper.Tiles.SubOddCopy
