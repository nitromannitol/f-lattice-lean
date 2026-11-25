import FLatticePaper.Plane.Induction.PhaseOneA
import FLatticePaper.Plane.Induction.TipReflect
import FLatticePaper.Plane.Induction.FreeHPrice
import FLatticePaper.Plane.Induction.EHPrice
import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.SheetPieces

/-! The phase-one price at the prescribed neighbour of a non-`H_0` free H root:
`P(i) = c₀ − 1 − min 0 (Ψ(reflH i) − 1)`, from `EHPrice.price_W1` with its four site facts:
* `F i = 0` (`neighbour_F_zero`),
* `F (i − tip) = F (reflH i + tip)` (`refl_tip`, under the word's packet),
* `A (reflH i) = 0` (`PhaseOneA.A_refl_zero`),
* the sheet-minimum identity at `reflH i + tip` (`tip_closed_reflH_W1`, `standardField_eq_sheetMin_of_strong`). -/

namespace FLatticePaper.PhaseOnePrice

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.PriceInputs
  FLatticePaper.Induction.TipVertex

theorem price_neighbour_W1 {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) {r : Site} (hr : r ∈ (frameAt word).freeH) (hr1 : r ≠ hFirst) {η : ℤ}
    (hη : η = 1 ∨ η = -1) :
    (frameAt word).price (standardField word) (r + (frameAt word).prescribedH η r) =
      (frameAt word).cutPrice - 1 -
        min 0 (sheetPsi word (FLatticePaper.ArcPsi.reflH word (r + (frameAt word).prescribedH η r)) - 1) := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := pdata h
  have hpk := packet_of_strong h hSE
  have hz0 := FLatticePaper.FreeHPrice.neighbour_F_zero (frameAt word) hpk.strips hr hη
  have hR := refl_tip (frameAt word) (standardField word) hpk (r + (frameAt word).prescribedH η r)
  have hA0w := FLatticePaper.PhaseOneA.A_refl_zero h hSE hW1 hr hr1 η
  have hcl := FLatticePaper.TipReflect.tip_closed_reflH_W1 (frameAt word) hN1 hND hD2 hnq hdq hn_eq hd_eq heps hW1 hr hη
  have hFVw := standardField_eq_sheetMin_of_strong h hSE hcl
  exact FLatticePaper.EHPrice.price_W1 h hSE hW1 _ hz0 hR hA0w hFVw

end FLatticePaper.PhaseOnePrice
