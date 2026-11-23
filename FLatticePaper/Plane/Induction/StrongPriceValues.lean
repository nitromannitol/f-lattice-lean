import FLatticePaper.Plane.Induction.I3CSheet
import FLatticePaper.Plane.Induction.OpenLocal
import FLatticePaper.Plane.Induction.W1Lower

/-! Task 66: the price and slip facts of STRONG_PRICE_AND_ALTERNATE_STEP §§1–3 that are proved here.

§1, the V star: on a site whose two sources (the site and its parent shift `z − v`) carry the harmonic grid `h0` (the true zero/h0 strips),
the primitive price is the constant `cutPrice` (`price_eq_cutPrice_of_harmonic`, from the polynomial identity `harmonicGrid_shift_price`).

§2–3, the rounded slip `J_η = ⌈D_η/2⌉`: it is monotone in `D_η` (`roundedSlip_mono`). The monotonicity of `D_η` itself on the selected white
edge is the note's comparison, not proved here.

§4 remainder, the recurrence of `M = min(A, C)`: it follows from the strong estimates of the conjugate (`sheetMin_recurrent_of_strong`):
`i3_sheetLocalInputs_of_strong` supplies the sheet local inputs, and the constrained burning ranks of `A` and `C` give the recurrence
(`sheetMin_binary_recurrent_of_chain`). No new input is needed for `M` beyond the conjugate's strong estimates. -/

namespace FLatticePaper.StrongPriceValues

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Lower

/-- **The V-star value.** If the field equals `h0` at a site and at its parent shift `z − v`, the primitive price there is `cutPrice`. -/
theorem price_eq_cutPrice_of_harmonic (frame : ChildFrame) (F : Field) (z : Site)
    (h1 : F z = harmonicGrid z) (h2 : F (z - frame.parentShift) = harmonicGrid (z - frame.parentShift)) :
    frame.price F z = frame.cutPrice := by
  have hd := delta_eq_price frame F z
  simp only [h1, h2, sub_self] at hd
  linarith

/-- The rounded slip is monotone in the slip. -/
theorem roundedSlip_mono (frame : ChildFrame) (F : Field) (η : ℤ) {i c : Site}
    (h : frame.slip F η i ≤ frame.slip F η c) : frame.roundedSlip F η i ≤ frame.roundedSlip F η c := by
  unfold ChildFrame.roundedSlip
  omega

/-- **The recurrence of the sheet minimum from the conjugate's strong estimates.** -/
theorem sheetMin_recurrent_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    Recurrent ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) := by
  have hsheet := i3_sheetLocalInputs_of_strong h hSE
  have hG := hSE.packet
  obtain ⟨rankA, hrankA⟩ := constrainedRank_of_variant h hG (i3aGrade_deck h hG)
    (permitA_invariant h hG) hsheet.permitA hsheet.noA
  obtain ⟨rankC, hrankC⟩ := constrainedRank_of_variant h hG (tGrade_add_odd_deck word)
    (permitC_invariant h hG) hsheet.permitC hsheet.noC
  exact (sheetMin_binary_recurrent_of_chain h hG hsheet.unit rankA rankC hrankA hrankC).2


/-- The sheet minimum of the conjugate's strong estimates is binary and recurrent. -/
theorem sheetMin_binary_recurrent_of_strong {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    (∀ z, laplacian ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) z = -1 ∨
        laplacian ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) z = 0) ∧
      Recurrent ((frameAt word).sheetMin (quarterTurnField (standardField (conjWord word)))) := by
  have hsheet := i3_sheetLocalInputs_of_strong h hSE
  have hG := hSE.packet
  obtain ⟨rankA, hrankA⟩ := constrainedRank_of_variant h hG (i3aGrade_deck h hG)
    (permitA_invariant h hG) hsheet.permitA hsheet.noA
  obtain ⟨rankC, hrankC⟩ := constrainedRank_of_variant h hG (tGrade_add_odd_deck word)
    (permitC_invariant h hG) hsheet.permitC hsheet.noC
  exact sheetMin_binary_recurrent_of_chain h hG hsheet.unit rankA rankC hrankA hrankC

end FLatticePaper.StrongPriceValues
