import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.W1Lower
import FLatticePaper.Plane.Induction.W1SeedFields
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.SlipFields
import FLatticePaper.Plane.Induction.Q3Field
import FLatticePaper.Plane.Induction.W1MSheet
import FLatticePaper.Plane.Induction.W1Seeds

/-! # Task 101 (3): the strips of the proper word restated for the sheet minimum `M = MW word` on the closed polygon

The word's own standard field `F = standardField word` satisfies the strip lemmas of `W1Strips` / `W1Lower` with these inputs, which are
checked here:

* the packet `(frameAt word).Packet F` (`packet_of_strong`): periods (with the kernel constant `0`), strips, reflection, binarity;
* the reflection `F (I − z) = F z` (`packet_reflection_I`, `iRefl_eq_sub`);
* the slip range `0 ≤ D₁ ≤ 2` on the closed polygon (`slipFields_of_strong`, with the named arc inputs `VArcInputs`);
* the even seed `F = 0` on `t = 2 − L` (`seedFields_of_conj`, from the induction hypothesis `SeedFields (conjWord word)`).

These give the even zero interval (`even_zero_full`), the top collar (`top_collar_zero_full`) and the V side and upper odd h0
(`V_side_full`, `odd_h0_upper`, which need the lower odd h0 `hlowW`). The lower odd h0 is `lower_odd_h0` with its own named hypotheses for
the word: the price range on the closed polygon, the price drifts, and the odd seed on `s = 2 − 3d + n`. The statements for `M` are the
word-level ones transported through `standardField_eq_sheetMin_of_strong` on the closed polygon. -/

namespace FLatticePaper.StripsM

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Strips FLatticePaper.W1MSheet FLatticePaper.W1Seeds

variable {word : Word}

/-- The periods of the standard field of the word (the kernel constant is zero). -/
theorem hper_word (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) :
    HasGeneratorPeriods (frameAt word).child (standardField word) 0 (frameAt word).coherentConstantV := by
  have hp := (packet_of_strong hw hSE).periods
  rw [coherentConstantU_eq_zero (frameAt word)] at hp
  exact hp

/-- The reflection `I` of the standard field of the word. -/
theorem hIsym_word (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word)) (z : Site) :
    standardField word (iRefl z) = standardField word z := by
  rw [iRefl_eq_sub]
  exact packet_reflection_I (frameAt word) (packet_of_strong hw hSE) z

/-- The slip range of the standard field of the word on the closed polygon, from the arc inputs. -/
theorem hslip_word (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (arcs : VArcInputs (frameAt word) (standardField word)) :
    ∀ z ∈ (frameAt word).closedPolygon, 0 ≤ (frameAt word).slip (standardField word) 1 z :=
  fun z hz => ((slipFields_of_strong hw hSE arcs).2.2 z hz).1

/-- The even seed of the standard field of the word, from the induction hypothesis on the conjugate. -/
theorem hseed_word (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpar : SeedFields (conjWord word)) :
    ∀ z : Site, EvenSite z → (frameAt word).tGrade z = 2 - ((frameAt word).child.den + (frameAt word).child.num) →
      standardField word z = 0 :=
  (FLatticePaper.W1SeedFields.seedFields_of_conj hw hSE hpar).even_zero

/-- **The even zero interval of `M`** (`even_zero_full`, transported to `M` on the closed polygon). -/
theorem even_zero_M (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpar : SeedFields (conjWord word)) (arcs : VArcInputs (frameAt word) (standardField word))
    (z : Site) (hz : z ∈ (frameAt word).closedPolygon) (he : EvenSite z)
    (hlo : 2 - ((frameAt word).child.den + (frameAt word).child.num) ≤ (frameAt word).tGrade z)
    (hhi : (frameAt word).tGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 2) :
    (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) z = 0 := by
  rw [← standardField_eq_sheetMin_of_strong hw hSE hz]
  exact even_zero_full (frameAt word) (hper_word hw hSE) (packet_of_strong hw hSE).strips
    (hslip_word hw hSE arcs) (hseed_word hw hSE hpar) (hIsym_word hw hSE) z he hlo hhi

/-- **The top collar of `M`** (`top_collar_zero_full`, transported to `M` on the closed polygon). -/
theorem top_collar_M (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hpar : SeedFields (conjWord word)) (arcs : VArcInputs (frameAt word) (standardField word))
    (y : Site) (hy : y ∈ (frameAt word).closedPolygon)
    (hyr : (EvenSite y ∧ (frameAt word).child.den + (frameAt word).child.num - 2 < (frameAt word).tGrade y ∧
        (frameAt word).tGrade y ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 2) ∨
      (¬ EvenSite y ∧ (frameAt word).child.den < (frameAt word).tGrade y ∧
        (frameAt word).tGrade y ≤ (frameAt word).child.num + 2 * (frameAt word).child.den - 2)) :
    (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) y = 0 := by
  rw [← standardField_eq_sheetMin_of_strong hw hSE hy]
  exact top_collar_zero_full (frameAt word) (hper_word hw hSE) (packet_of_strong hw hSE).strips
    (hslip_word hw hSE arcs) (hseed_word hw hSE hpar) (hIsym_word hw hSE) y hyr

/-- **The lower odd h0 of the standard field of the word** (`lower_odd_h0`), from its named hypotheses for the word. -/
theorem hlowW_of_named (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hPR : ∀ z ∈ (frameAt word).closedPolygon, (frameAt word).cutPrice - 1 ≤ (frameAt word).price (standardField word) z ∧
      (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice)
    (hPU : ∀ z, (frameAt word).price (standardField word) (z + (frameAt word).child.modifiedDeck.kernel) =
      (frameAt word).price (standardField word) z - 1)
    (hPV : ∀ z, (frameAt word).price (standardField word) (z + (frameAt word).child.modifiedDeck.transverse) =
      (frameAt word).price (standardField word) z)
    (hseedOdd : ∀ w : Site, ¬ EvenSite w → (frameAt word).sGrade w = 2 - 3 * (frameAt word).child.den + (frameAt word).child.num →
      standardField word w = harmonicGrid w) :
    ∀ z : Site, ¬ EvenSite z → 2 - 3 * (frameAt word).child.den + (frameAt word).child.num ≤ (frameAt word).sGrade z →
      (frameAt word).sGrade z ≤ 1 - 2 * (frameAt word).child.den → standardField word z = harmonicGrid z :=
  fun z hz h1 h2 => FLatticePaper.W1Lower.lower_odd_h0 (frameAt word) (packet_of_strong hw hSE).strips hPR hPU hPV hseedOdd
    z hz h1 h2

/-- **The V side of `M`** (`V_side_full`, transported to `M` on the closed polygon), from the lower odd h0 `hlowW`. -/
theorem V_side_M (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hlowW : ∀ z : Site, ¬ EvenSite z → 2 - 3 * (frameAt word).child.den + (frameAt word).child.num ≤ (frameAt word).sGrade z →
      (frameAt word).sGrade z ≤ 1 - 2 * (frameAt word).child.den → standardField word z = harmonicGrid z)
    (z : Site) (hz : z ∈ (frameAt word).closedPolygon) (hodd : ¬ EvenSite z)
    (hlo : (frameAt word).child.den + (frameAt word).child.num - 2 < (frameAt word).sGrade z)
    (hhi : (frameAt word).sGrade z ≤ 3 * (frameAt word).child.den + (frameAt word).child.num - 2) :
    (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) z = harmonicGrid z := by
  rw [← standardField_eq_sheetMin_of_strong hw hSE hz]
  exact V_side_full (frameAt word) (packet_of_strong hw hSE).strips (hIsym_word hw hSE) hlowW z hodd hlo hhi

/-- **The upper odd h0 of `M`** (`odd_h0_upper`, transported to `M` on the closed polygon), from the lower odd h0 `hlowW`. -/
theorem odd_h0_upper_M (hw : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hlowW : ∀ z : Site, ¬ EvenSite z → 2 - 3 * (frameAt word).child.den + (frameAt word).child.num ≤ (frameAt word).sGrade z →
      (frameAt word).sGrade z ≤ 1 - 2 * (frameAt word).child.den → standardField word z = harmonicGrid z)
    (w : Site) (hw' : w ∈ (frameAt word).closedPolygon) (hodd : ¬ EvenSite w)
    (hlo : 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1 ≤ (frameAt word).sGrade w)
    (hhi : (frameAt word).sGrade w ≤ 3 * (frameAt word).child.den + (frameAt word).child.num - 2) :
    (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) w = harmonicGrid w := by
  rw [← standardField_eq_sheetMin_of_strong hw hSE hw']
  exact odd_h0_upper (frameAt word) (hIsym_word hw hSE) hlowW w hodd hlo hhi

end FLatticePaper.StripsM
