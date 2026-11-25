import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.HFVTip

/-! Task 72, the `hFV` hypothesis of `PriceDeck`/`price_W0`: the tip image of a free H site is a point where the field equals the sheet
minimum. For `z ∈ freeH`, `z + tipVertex` lies in the closed polygon (`HFVTip`), and `standardField = sheetMin` on the closed polygon
(`standardField_eq_sheetMin_of_strong`). -/

namespace FLatticePaper.FreeHSheetAgree

open Farey FLatticePaper FLatticePaper.Induction

/-- **`hFV` on the free H arc.** -/
theorem hFV_of_freeH {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hS : StrongEstimates (conjWord word))
    {z : Site} (hz : z ∈ (frameAt word).freeH) :
    standardField word (z + TipVertex.tipVertex (frameAt word)) =
      (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))
        (z + TipVertex.tipVertex (frameAt word)) :=
  standardField_eq_sheetMin_of_strong h hS (HFVTip.tipVertex_mem_closedPolygon (frameAt word) hz)

end FLatticePaper.FreeHSheetAgree
