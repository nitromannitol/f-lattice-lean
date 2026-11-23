import FLatticePaper.Plane.Induction.StrongPriceRange
import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.Potentials

/-! Task 68: the price range of a word from the conjugate's strong estimates alone, with the boundary bound as the only named input.

The packet of the word (`packet_of_strong`), the agreement `F = M` on `E` (`standardField_eq_sheetMin_of_strong`), the recurrence and binarity
of `M` (`sheetMin_binary_recurrent_of_strong`) and the drifts of `P` (`price_kernel`, `price_transverse`, from the packet's periods) are all
derived from the conjugate's strong estimates. The boundary bound `P ≤ c₀` on `∂E` (the earlier priced boundary comparisons) remains named. -/

namespace FLatticePaper.StrongPriceInputs

open Farey FLatticePaper FLatticePaper.Induction

/-- **The price range from the conjugate's strong estimates.** -/
theorem priceRange_of_conjugate {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hbd : ∀ z, OnBoundary (frameAt word).closedPolygon z →
      (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice) :
    ∀ z ∈ (frameAt word).closedPolygon,
      (frameAt word).cutPrice - 1 ≤ (frameAt word).price (standardField word) z ∧
        (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice := by
  have hpk := packet_of_strong h hSE
  obtain ⟨hbinM, hrecM⟩ := FLatticePaper.StrongPriceValues.sheetMin_binary_recurrent_of_strong h hSE
  have hrec := recurrentField_of_recurrent hrecM hbinM
  have hagree : ∀ y ∈ (frameAt word).closedPolygon,
      standardField word y = (frameAt word).sheetMin (quarterTurnField (standardField (conjWord word))) y :=
    fun y hy => standardField_eq_sheetMin_of_strong h hSE hy
  exact FLatticePaper.StrongPriceRange.priceRange_of_recurrent (frameAt word) hagree hpk.binary hbinM hrec hbd
    hpk.reflection (fun w => (frameAt word).price_kernel (standardField word) hpk.periods w)
    (fun w => (frameAt word).price_transverse (standardField word) hpk.periods w)


/-- **The boundary value `c₀` on the h0 strip window.** If `F` carries the ordinary h0 strip and `s(z) ∈ [3 − 2d, 2L − 1]`, then both `z` and
`z − v` lie in the window `[1 − 2d, 2L − 1]` (since `s(v) = 2`), so `F = h0` there and `P z = c₀`. -/
theorem price_eq_cutPrice_of_hWindow (frame : ChildFrame) (F : Field) (hS : frame.HasStrips F) (z : Site)
    (hs1 : 3 - 2 * frame.child.den ≤ frame.sGrade z)
    (hs2 : frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1) :
    frame.price F z = frame.cutPrice := by
  obtain ⟨-, hh⟩ := hS
  have hV := FLatticePaper.StrongPriceRange.sGrade_parentShift frame
  have hlin : frame.sGrade (z - frame.parentShift) = frame.sGrade z - frame.sGrade frame.parentShift := by
    unfold ChildFrame.sGrade
    simp only [Prod.fst_sub, Prod.snd_sub]
    ring
  have hsub : frame.sGrade (z - frame.parentShift) = frame.sGrade z - 2 := by rw [hlin, hV]
  have h1 : F z = harmonicGrid z := hh z (by omega) hs2
  have h2 : F (z - frame.parentShift) = harmonicGrid (z - frame.parentShift) :=
    hh (z - frame.parentShift) (by rw [hsub]; omega) (by rw [hsub]; omega)
  exact FLatticePaper.StrongPriceValues.price_eq_cutPrice_of_harmonic frame F z h1 h2


/-- **The zero-source boundary identity.** If `F z = 0` (the zero strip at `z`) and `F (z − v) = h₀ (z − v)`, then `P z = c₀ − h₀ z`. -/
theorem price_eq_cutPrice_sub_harmonic_of_zero (frame : ChildFrame) (F : Field) (z : Site) (h0z : F z = 0)
    (h1 : F (z - frame.parentShift) = harmonicGrid (z - frame.parentShift)) :
    frame.price F z = frame.cutPrice - harmonicGrid z := by
  have hd := FLatticePaper.W1Lower.harmonicGrid_shift_price frame z
  unfold ChildFrame.price ChildFrame.parentSlope
  rw [h0z, h1]
  linarith

/-- On such a site, `P z ≤ c₀` exactly when `h₀ z ≥ 0`. -/
theorem price_le_cutPrice_iff_harmonic_nonneg (frame : ChildFrame) (F : Field) (z : Site) (h0z : F z = 0)
    (h1 : F (z - frame.parentShift) = harmonicGrid (z - frame.parentShift)) :
    frame.price F z ≤ frame.cutPrice ↔ 0 ≤ harmonicGrid z := by
  rw [price_eq_cutPrice_sub_harmonic_of_zero frame F z h0z h1]
  constructor <;> intro h <;> linarith

end FLatticePaper.StrongPriceInputs
