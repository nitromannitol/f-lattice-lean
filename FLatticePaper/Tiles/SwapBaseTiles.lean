import FLatticePaper.Tiles.JointInduction
import FLatticePaper.Tiles.WeakStepPaper

/-! # The base tile odometers of the paper family

At a base word the tile odometers of a good family are the weak odometers (`TilePart`), and the weak odometers satisfy the base
condition `D.S.base` (`WeakPart`). For the paper data `D.S = paperS`, whose base condition is `PaperBaseCond`. -/

namespace FLatticePaper.Tiles.SwapBaseTiles

open FLatticePaper.Farey FLatticePaper.Tiles.JointFamily FLatticePaper.Tiles.JointInduction FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.WeakStepPaper

/-- The standard tile odometers of a base word of length below `n`, in a good family for the paper data, satisfy the paper
base condition. -/
theorem base_tiles_paper (D : JointData) (hS : D.S = paperS) (f : Word → JSlice) (n : ℕ)
    (hG : GoodBelow D f n) (u : Word) (hu : u.length < n) (hb : FLatticePaper.Tiles.Standard.IsBase u) :
    PaperBaseCond u (f u).tOdd (f u).tEven := by
  obtain ⟨hJ, -⟩ := hG u hu
  obtain ⟨hW, -, hT, -⟩ := hJ
  have hbase := hW.2.2.1 hb
  rw [hS] at hbase
  obtain ⟨h1, h2, -⟩ := hT.1 hb
  rw [h1, h2]
  exact hbase

end FLatticePaper.Tiles.SwapBaseTiles
