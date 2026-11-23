import FLatticePaper.Plane.Induction.SheetCharts
import FLatticePaper.Plane.Induction.StrongBridge
import FLatticePaper.Construction.NominalAgreement

/-! Task 65, item (1): the standard field is its sheet minimum on the star.

* `standardField_eq_sheetMin_of_strong`: on the closed polygon `E`, the standard field of a proper word equals the sheet
  minimum `min(A, C)`. The `RespectsPeriodsOn` hypothesis of `standardField_eq_sheetMin` is discharged from the strong
  estimates of the conjugate, through the same chain as `arcInputs_of_strong` (`openInputs_of_strong`,
  `sheetFacts_of_conjPacket`, `stripInputs_sheetMin`, `respectsPeriodsOn_of_heightInputs`).
* `standardField_eq_sheetMin_on_star`: if a centre and its two inputs lie in `E` (paragraph 2 for a black centre), the
  standard field is the sheet minimum at the centre and at both inputs. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem standardField_eq_sheetMin_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word)) {s : Site} (hs : s ∈ (frameAt word).closedPolygon) :
    standardField word s =
      (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) s := by
  have hO := openInputs_of_strong h hS
  obtain ⟨hA0, hEq, hrefl, -⟩ := sheetFacts_of_conjPacket h hS.packet
  obtain ⟨hC0, hGe, -⟩ := hO
  have hSt := (frameAt word).stripInputs_sheetMin hA0 hC0 hEq hGe hrefl
  exact Construction.standardField_eq_sheetMin h hs
    ((frameAt word).respectsPeriodsOn_of_heightInputs hSt.heightInputs)

/-- On the star of a centre `z` whose two inputs lie in `E` (paragraph 2): the standard field is the sheet minimum at
`z` and at both inputs. -/
theorem standardField_eq_sheetMin_on_star {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word)) {z i u : Site} (hz : z ∈ (frameAt word).closedPolygon)
    (hi : i ∈ (frameAt word).closedPolygon) (hu : u ∈ (frameAt word).closedPolygon) :
    standardField word z = (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) z ∧
      standardField word i = (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) i ∧
      standardField word u = (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) u :=
  ⟨standardField_eq_sheetMin_of_strong h hS hz, standardField_eq_sheetMin_of_strong h hS hi,
    standardField_eq_sheetMin_of_strong h hS hu⟩

end FLatticePaper.Induction
