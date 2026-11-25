import FLatticePaper.Plane.Induction.WhiteSheet
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.SheetOffsets
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.W1MSheet

/-! # W0 on the sheets, for `ε = +1`

At `ε = +1` the sheet `A` in standard coordinates is the quarter-turn field itself (`sheetA_pos`), and the standard field is the
sheet minimum on the closed polygon (`standardField_eq_sheetMin_of_strong`). So at a white point `z` of the standard field that is
an `A`-root (`F z = FqW z`), both inputs are `A`-roots: `WhiteSheet.agree_at_white` with `A = FqW`. -/

namespace FLatticePaper.WhiteSheetPlus

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet

/-- **The inputs of an `A`-root white are `A`-roots (`ε = +1`).** -/
theorem inputs_aroot_plus {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hε : (frameAt word).eps = 1) {z : Site}
    (hF : laplacian (standardField word) z = 0) (hA : standardField word z = FqW word z)
    (hi : ∀ i : Site, (i = incomingNeg z ∨ i = incomingPos z) → i ∈ (frameAt word).closedPolygon) :
    ∀ i : Site, (i = incomingNeg z ∨ i = incomingPos z) →
      standardField word i = FqW word i ∧ laplacian (FqW word) z = 0 := by
  have hbin : ∀ x, laplacian (quarterTurnField (standardField (conjWord word))) x = -1 ∨
      laplacian (quarterTurnField (standardField (conjWord word))) x = 0 :=
    fun x => quarterTurnField_binary hSE.packet.binary x
  have hle : ∀ i : Site, (i = incomingNeg z ∨ i = incomingPos z) → standardField word i ≤ FqW word i := by
    intro i hi'
    rw [standardField_eq_sheetMin_of_strong h hSE (hi i hi')]
    unfold ChildFrame.sheetMin
    rw [FLatticePaper.SheetOffsets.sheetA_pos hε]
    exact min_le_left _ _
  have key := FLatticePaper.WhiteSheet.agree_at_white (F := standardField word) (A := FqW word) (z := z)
    (hbin z) hF hA hle
  intro i hi'
  rcases hi' with rfl | rfl
  · exact ⟨key.1, key.2.2⟩
  · exact ⟨key.2.1, key.2.2⟩

end FLatticePaper.WhiteSheetPlus
