import FLatticePaper.Plane.Induction.StripsM
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.NativeCongruence
import FLatticePaper.Plane.Induction.Potentials

/-! # W4 (Q35): the slip `D'_η` of the conjugate vanishes on its native free H points

Q35 (display (1)): `D'_ε = 0` on the native H points, because their grades and their shifts by `±2` lie in the ordinary zero strip
`[1 − d', n' + 2d' − 1]` of the conjugate's own standard field (`d' = den`, `n' = num` of the conjugate child).

The own-frame strip is the `ChildFrame.zero_strip` of the conjugate frame, with the strip inputs `StripsM.stripInputs_M` (the sheet
minimum of the quarter turn of the grand-conjugate field), the agreement `standardField_eq_sheetMin_of_strong` on the closed polygon, and
the periods `StripsM.hper_word`. These use the two inputs of the trace induction: `hX : ∃ x ∈ conjWord word, x ≠ three` and
`hSE' : StrongEstimates (conjWord (conjWord word))`. -/

namespace FLatticePaper.W4NativeSlip

open Farey FLatticePaper FLatticePaper.Induction

variable {word : Word}

/-- **The own zero strip of the conjugate's standard field.** On `1 − d' ≤ t' ≤ n' + 2d' − 1` (own grades) the field vanishes. -/
theorem conj_standardField_zero_strip (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE' : StrongEstimates (conjWord (conjWord word))) {z : Site}
    (hlo : 1 - (frameAt (conjWord word)).child.den ≤ (frameAt (conjWord word)).tGrade z)
    (hhi : (frameAt (conjWord word)).tGrade z ≤
      (frameAt (conjWord word)).child.num + 2 * (frameAt (conjWord word)).child.den - 1) :
    standardField (conjWord word) z = 0 :=
  (frameAt (conjWord word)).zero_strip (StripsM.stripInputs_M hX hSE')
    (fun _ hy => standardField_eq_sheetMin_of_strong hX hSE' hy) (StripsM.hper_word hX hSE') z hlo hhi

/-- The grade of a `±1` multiple of the short shift: `t(z + η σ) = t(z) − 2η`. -/
theorem tGrade_add_smul_shortShift (frame : ChildFrame) (z : Site) (η : ℤ) :
    frame.tGrade (z + η • frame.shortShift) = frame.tGrade z - 2 * η := by
  rw [frame.tGrade_add_pt, FLatticePaper.NativeCongruence.tGrade_shortShift_smul frame η]
  ring

/-- A free H point has `t` with room for the `±2` shifts inside the zero strip: `3 − d ≤ t ≤ n + 2d − 3`. -/
theorem freeH_strip_margin (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) :
    3 - frame.child.den ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 3 := by
  obtain ⟨hn0, -, -, hd3, -⟩ := frame.child_facts
  have hsp : frame.hSpectrum (frame.tGrade z) := hz.2.2
  unfold ChildFrame.hSpectrum at hsp
  rcases hsp with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩ <;> constructor <;> omega

/-- **`D'_η = 0` on the native free H points of the conjugate (Q35).** For `η = ±1`, the slip of the conjugate's standard field vanishes
at every conjugate free H point: both `z` and `z + η σ'` lie in the own zero strip. -/
theorem conj_slip_zero_native_H (hX : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE' : StrongEstimates (conjWord (conjWord word))) {z : Site}
    (hz : z ∈ (frameAt (conjWord word)).freeH) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    (frameAt (conjWord word)).slip (standardField (conjWord word)) η z = 0 := by
  obtain ⟨hA, hB⟩ := freeH_strip_margin (frameAt (conjWord word)) hz
  have hz0 : standardField (conjWord word) z = 0 :=
    conj_standardField_zero_strip hX hSE' (by omega) (by omega)
  have hy : standardField (conjWord word) (z + η • (frameAt (conjWord word)).shortShift) = 0 := by
    refine conj_standardField_zero_strip hX hSE' ?_ ?_
    · rw [tGrade_add_smul_shortShift]
      rcases hη with rfl | rfl <;> omega
    · rw [tGrade_add_smul_shortShift]
      rcases hη with rfl | rfl <;> omega
  unfold ChildFrame.slip
  rw [hz0, hy]
  ring

/-- **`D'_η = 0` on the native free H points of the conjugate, from the conjugate's own packet.** The zero band of the conjugate's
standard field is the `HasStrips` of its packet `hSE.packet`, so neither properness of the conjugate nor the grand conjugate's estimates
is needed. -/
theorem conj_slip_zero_native_H_packet {word : Word} (hSE : StrongEstimates (conjWord word)) {z : Site}
    (hz : z ∈ (frameAt (conjWord word)).freeH) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    (frameAt (conjWord word)).slip (standardField (conjWord word)) η z = 0 := by
  obtain ⟨hA, hB⟩ := freeH_strip_margin (frameAt (conjWord word)) hz
  have hz0 : standardField (conjWord word) z = 0 := hSE.packet.strips.1 z (by omega) (by omega)
  have hy : standardField (conjWord word) (z + η • (frameAt (conjWord word)).shortShift) = 0 := by
    refine hSE.packet.strips.1 _ ?_ ?_
    · rw [tGrade_add_smul_shortShift]
      rcases hη with rfl | rfl <;> omega
    · rw [tGrade_add_smul_shortShift]
      rcases hη with rfl | rfl <;> omega
  unfold ChildFrame.slip
  rw [hz0, hy]
  ring

end FLatticePaper.W4NativeSlip
