import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.W1Lower
import FLatticePaper.Plane.Induction.W1SeedFields
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.SlipFields
import FLatticePaper.Plane.Induction.Q3Field
import FLatticePaper.Plane.Induction.W1MSheet
import FLatticePaper.Plane.Induction.W1Seeds
import FLatticePaper.Plane.Induction.ParentStepDischarge
import FLatticePaper.Plane.Induction.StrongPriceInputs
import FLatticePaper.Plane.Induction.StrongBridge
import FLatticePaper.Plane.Induction.SheetFacts
import FLatticePaper.Plane.Induction.Step
import FLatticePaper.Plane.Induction.Strips

/-! # Task 101 (3), wired: the strips of the proper word restated for the sheet minimum `M = MW word` on the closed polygon

Every input is derived from the conjugate's strong estimates, except the named ones below:

* the packet `(frameAt word).Packet (standardField word)` (`packet_of_strong`), its periods (kernel constant `0`), strips, reflection;
* the arc inputs `VArcInputs (frameAt word) (standardField word)`, discharged (`vArcInputs_of_strong_discharged`) from the strip inputs of
  `M` (`sheetFacts_of_conjPacket`, `openInputs_of_strong`, `stripInputs_sheetMin`) and the height inputs (`StripInputs.heightInputs`);
* the slip range on the closed polygon (`slipFields_of_strong`) and the even seed (`seedFields_of_conj`);
* the price range of the word (`priceRange_of_conjugate`, from the conjugate's estimates and the recurrence of `M`, with its boundary bound
  `hbd` as the named input) and the price drifts of the word (`price_kernel`, `price_transverse` from the packet).

The lower odd h0 `hlowW` takes the odd seed `hseedOdd` as its named input (the seed of the word's own field on `s = 2 − 3d + n`). The
dependency order is acyclic: nothing here uses `W1` at the word itself. -/

namespace FLatticePaper.StripsM

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Strips FLatticePaper.W1MSheet FLatticePaper.W1Seeds
open FLatticePaper.StrongPriceInputs

/-- The periods of the standard field of the word (the kernel constant is zero). -/
theorem hper_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    HasGeneratorPeriods (frameAt word).child (standardField word) 0 (frameAt word).coherentConstantV := by
  have hp := (packet_of_strong hw hSE).periods
  rw [coherentConstantU_eq_zero (frameAt word)] at hp
  exact hp

/-- The reflection `I` of the standard field of the word. -/
theorem hIsym_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) (z : Site) :
    standardField word (iRefl z) = standardField word z := by
  rw [iRefl_eq_sub]
  exact packet_reflection_I (frameAt word) (packet_of_strong hw hSE) z

/-- The strip inputs of the sheet minimum `M`, from the conjugate's estimates (`sheetFacts_of_conjPacket`, `openInputs_of_strong`). -/
theorem stripInputs_M {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    (frameAt word).StripInputs ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) := by
  obtain ⟨hA0, hEq, hrefl, -⟩ := sheetFacts_of_conjPacket hw hSE.packet
  obtain ⟨hC0, hGe, -⟩ := openInputs_of_strong hw hSE
  exact (frameAt word).stripInputs_sheetMin hA0 hC0 hEq hGe hrefl

/-- **The arc inputs of the word**, discharged from the conjugate's estimates (no named input). -/
theorem arcs_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    VArcInputs (frameAt word) (standardField word) :=
  vArcInputs_of_strong_discharged hw hSE (stripInputs_M hw hSE) (stripInputs_M hw hSE).heightInputs
    (fun _ hy => standardField_eq_sheetMin_of_strong hw hSE hy) (hper_word hw hSE)

/-- The slip range of the standard field of the word on the closed polygon. -/
theorem hslip_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    ∀ z ∈ (frameAt word).closedPolygon, 0 ≤ (frameAt word).slip (standardField word) 1 z :=
  fun z hz => ((slipFields_of_strong hw hSE (arcs_word hw hSE)).2.2 z hz).1

/-- The even seed of the standard field of the word, from the induction hypothesis on the conjugate. -/
theorem hseed_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpar : SeedFields (conjWord word)) :
    ∀ z : Site, EvenSite z → (frameAt word).tGrade z = 2 - ((frameAt word).child.den + (frameAt word).child.num) →
      standardField word z = 0 :=
  (FLatticePaper.W1SeedFields.seedFields_of_conj hw hSE hpar).even_zero

/-- **The even zero interval of `M`** (`even_zero_full`, transported to `M` on the closed polygon). -/
theorem even_zero_M {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpar : SeedFields (conjWord word))
    (z : Site) (hz : z ∈ (frameAt word).closedPolygon) (he : EvenSite z)
    (hlo : 2 - ((frameAt word).child.den + (frameAt word).child.num) ≤ (frameAt word).tGrade z)
    (hhi : (frameAt word).tGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 2) :
    (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) z = 0 := by
  rw [← standardField_eq_sheetMin_of_strong hw hSE hz]
  exact even_zero_full (frameAt word) (hper_word hw hSE) (packet_of_strong hw hSE).strips
    (hslip_word hw hSE) (hseed_word hw hSE hpar) (hIsym_word hw hSE) z he hlo hhi

/-- **The top collar of `M`** (`top_collar_zero_full`, transported to `M` on the closed polygon). -/
theorem top_collar_M {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpar : SeedFields (conjWord word))
    (y : Site) (hy : y ∈ (frameAt word).closedPolygon)
    (hyr : (EvenSite y ∧ (frameAt word).child.den + (frameAt word).child.num - 2 < (frameAt word).tGrade y ∧
        (frameAt word).tGrade y ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 2) ∨
      (¬ EvenSite y ∧ (frameAt word).child.den < (frameAt word).tGrade y ∧
        (frameAt word).tGrade y ≤ (frameAt word).child.num + 2 * (frameAt word).child.den - 2)) :
    (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) y = 0 := by
  rw [← standardField_eq_sheetMin_of_strong hw hSE hy]
  exact top_collar_zero_full (frameAt word) (hper_word hw hSE) (packet_of_strong hw hSE).strips
    (hslip_word hw hSE) (hseed_word hw hSE hpar) (hIsym_word hw hSE) y hyr

/-- **The lower odd h0 of the standard field of the word** (`lower_odd_h0`): the price range from `priceRange_of_conjugate` (boundary
bound `hbd` named), the price drifts from the packet, and the odd seed `hseedOdd` named. -/
theorem hlowW_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hbd : ∀ z, OnBoundary (frameAt word).closedPolygon z → (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice)
    (hseedOdd : ∀ w : Site, ¬ EvenSite w →
      (frameAt word).sGrade w = 2 - 3 * (frameAt word).child.den + (frameAt word).child.num →
      standardField word w = harmonicGrid w) :
    ∀ z : Site, ¬ EvenSite z → 2 - 3 * (frameAt word).child.den + (frameAt word).child.num ≤ (frameAt word).sGrade z →
      (frameAt word).sGrade z ≤ 1 - 2 * (frameAt word).child.den → standardField word z = harmonicGrid z :=
  fun z hz h1 h2 => FLatticePaper.W1Lower.lower_odd_h0 (frameAt word) (packet_of_strong hw hSE).strips
    (priceRange_of_conjugate hw hSE hbd)
    (fun w => (frameAt word).price_kernel (standardField word) (packet_of_strong hw hSE).periods w)
    (fun w => (frameAt word).price_transverse (standardField word) (packet_of_strong hw hSE).periods w)
    hseedOdd z hz h1 h2

/-- **The V side of `M`** (`V_side_full`, transported to `M` on the closed polygon), from the lower odd h0 `hlowW`. -/
theorem V_side_M {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hlowW : ∀ z : Site, ¬ EvenSite z → 2 - 3 * (frameAt word).child.den + (frameAt word).child.num ≤ (frameAt word).sGrade z →
      (frameAt word).sGrade z ≤ 1 - 2 * (frameAt word).child.den → standardField word z = harmonicGrid z)
    (z : Site) (hz : z ∈ (frameAt word).closedPolygon) (hodd : ¬ EvenSite z)
    (hlo : (frameAt word).child.den + (frameAt word).child.num - 2 < (frameAt word).sGrade z)
    (hhi : (frameAt word).sGrade z ≤ 3 * (frameAt word).child.den + (frameAt word).child.num - 2) :
    (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) z = harmonicGrid z := by
  rw [← standardField_eq_sheetMin_of_strong hw hSE hz]
  exact V_side_full (frameAt word) (packet_of_strong hw hSE).strips (hIsym_word hw hSE) hlowW z hodd hlo hhi

/-- **The upper odd h0 of `M`** (`odd_h0_upper`, transported to `M` on the closed polygon), from the lower odd h0 `hlowW`. -/
theorem odd_h0_upper_M {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hlowW : ∀ z : Site, ¬ EvenSite z → 2 - 3 * (frameAt word).child.den + (frameAt word).child.num ≤ (frameAt word).sGrade z →
      (frameAt word).sGrade z ≤ 1 - 2 * (frameAt word).child.den → standardField word z = harmonicGrid z)
    (w : Site) (hw' : w ∈ (frameAt word).closedPolygon) (hodd : ¬ EvenSite w)
    (hlo : 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1 ≤ (frameAt word).sGrade w)
    (hhi : (frameAt word).sGrade w ≤ 3 * (frameAt word).child.den + (frameAt word).child.num - 2) :
    (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) w = harmonicGrid w := by
  rw [← standardField_eq_sheetMin_of_strong hw hSE hw']
  exact odd_h0_upper (frameAt word) (hIsym_word hw hSE) hlowW w hodd hlo hhi

end FLatticePaper.StripsM
