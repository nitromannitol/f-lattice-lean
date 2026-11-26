import FLatticePaper.Plane.Induction.StrongResidualStep
import FLatticePaper.Plane.Induction.StrongBridge
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! # The strong estimates of a word before its games

`StrongEstimates u` has one field, `F2F3_policy`, that needs the signed policies of the word `u` itself. Every other field comes
from the strong estimates of the conjugate word, the boundary price bound of `u` and the seed fields of the conjugate
(`strongEstimates_step_strong`, `strongResidual_of_conj`). `StrongCore u` (StrongCoreDef) is the structure of these other fields.
`strongCore_of_conj` builds it at a proper word that is not a two-power, so the games of the word can be constructed
from it before the strong estimates of the word are assembled. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- **The core of the strong estimates of a proper word that is not a two-power**, from the conjugate's strong estimates, the
boundary price bound and the conjugate's seed fields. The fields are those of `strongEstimates_step_strong` and
`strongResidual_of_conj`, which do not use the policy of the word. -/
theorem strongCore_of_conj {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (h2 : ∃ x ∈ word, x ≠ Digit.two)
    (hSE : StrongEstimates (conjWord word))
    (hbd : ∀ z, OnBoundary (frameAt word).closedPolygon z →
      (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice)
    (hpar : FLatticePaper.W1Seeds.SeedFields (conjWord word)) :
    StrongCore word := by
  have hpk : (frameAt word).Packet (standardField word) := FLatticePaper.Induction.packet_of_strong h hSE
  have hSeeds := FLatticePaper.W1SeedFields.seedFields_of_conj h hSE hpar
  have hseed : ∀ w : Site, ¬ EvenSite w →
      (frameAt word).sGrade w = 2 - 3 * (frameAt word).child.den + (frameAt word).child.num →
        standardField word w = harmonicGrid w :=
    fun w hw hs => hSeeds.odd_bottom w hw hs
  have hPR := FLatticePaper.StrongPriceInputs.priceRange_of_conjugate h hSE hbd
  have hPU : ∀ z, (frameAt word).price (standardField word) (z + (frameAt word).child.modifiedDeck.kernel) =
      (frameAt word).price (standardField word) z - 1 :=
    fun z => (frameAt word).price_kernel (standardField word) hpk.periods z
  have hPV : ∀ z, (frameAt word).price (standardField word) (z + (frameAt word).child.modifiedDeck.transverse) =
      (frameAt word).price (standardField word) z :=
    fun z => (frameAt word).price_transverse (standardField word) hpk.periods z
  have hSU : ∀ η : ℤ, ∀ z, (frameAt word).slip (standardField word) η
      (z + (frameAt word).child.modifiedDeck.kernel) = (frameAt word).slip (standardField word) η z :=
    fun η z => (frameAt word).slip_kernel (standardField word) hpk.periods η z
  have hSV : ∀ η : ℤ, ∀ z, (frameAt word).slip (standardField word) η
      (z + (frameAt word).child.modifiedDeck.transverse) = (frameAt word).slip (standardField word) η z + 2 * η :=
    fun η z => (frameAt word).slip_transverse (standardField word) hpk.periods η z
  have hZE := FLatticePaper.W1ZeroStrip.zeroEvenLine_field word hpk hPR hPU hPV hseed
  have hn3 : 3 ≤ (frameAt word).child.num := FLatticePaper.Farey.current_even_num_ge_three word h
  have hd4 : 4 ≤ (frameAt word).child.den - (frameAt word).child.num :=
    FLatticePaper.Farey.current_even_diff_ge_four word h2
  have hcls := FLatticePaper.StrongUnitPrice.starClassified_of_grades (frameAt word) (standardField word) hn3 hd4 hpk.strips
  have hU := FLatticePaper.StrongUnitPrice.unitPrice_and_noSaddle (frameAt word) (standardField word) hPR hPU hPV hcls
  have hslip := slipFields_of_strong h hSE (arcInputs_of_strong h hSE)
  exact
    { packet := packet_of_openInputs_step h hSE.packet (openInputs_of_strong h hSE)
      slipRange := hslip.2.2
      priceRange := hPR
      priceDrift := fun z => ⟨by linarith [hPU z], by linarith [hPV z]⟩
      slipDrift := fun η _ z => ⟨by linarith [hSU η z], by linarith [hSV η z]⟩
      zeroStripInterval := FLatticePaper.W1ZeroStrip.zeroStripInterval_of_packet word hpk
      zeroEvenLine := hZE
      F1_unitSlip := hslip.1
      F1_noSlipSaddle := hslip.2.1
      F1_unitPrice := hU.1
      F1_noPriceSaddle := hU.2 }

end FLatticePaper.Induction
