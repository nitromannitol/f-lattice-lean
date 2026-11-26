import FLatticePaper.Plane.Induction.WordBoundary
import FLatticePaper.Plane.Induction.W4NativeSlip

/-! # Slips that vanish on the zero band of the word's standard field (the free H boundary of the forced-edge permit)

The standard field of the word vanishes on the t-band `[1 − d, n + 2d − 1]` (`WordBoundary.standardField_zero_strip_word`). Hence the raw slip
`D_η(z) = F z − F (z + η σ)` vanishes wherever both `z` and `z + η σ` lie in the band, for either sign. At a free H site both lie in the band
(`W4NativeSlip.freeH_strip_margin`), so the slip vanishes there. These give the permit with equality on the forced edges whose four points
lie in the band (the sign −1 boundary edges of the forced permit). -/

namespace FLatticePaper.BoundarySlip

open Farey FLatticePaper FLatticePaper.Induction

/-- **The slip vanishes on the zero band.** If `z` and `z + η σ` lie in the t-band of the word, `D_η(z) = 0`. -/
theorem slip_eq_zero_of_band_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {η : ℤ} {z : Site}
    (h1 : 1 - (frameAt word).child.den ≤ (frameAt word).tGrade z)
    (h2 : (frameAt word).tGrade z ≤ (frameAt word).child.num + 2 * (frameAt word).child.den - 1)
    (h3 : 1 - (frameAt word).child.den ≤ (frameAt word).tGrade (z + η • (frameAt word).shortShift))
    (h4 : (frameAt word).tGrade (z + η • (frameAt word).shortShift) ≤
      (frameAt word).child.num + 2 * (frameAt word).child.den - 1) :
    (frameAt word).slip (standardField word) η z = 0 := by
  have hz := WordBoundary.standardField_zero_strip_word hw hSE h1 h2
  have hy := WordBoundary.standardField_zero_strip_word hw hSE h3 h4
  unfold ChildFrame.slip
  rw [hz, hy, sub_self]

/-- **The slip vanishes at a free H site, for either sign.** -/
theorem slip_eq_zero_freeH_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {η : ℤ} (hη : η = 1 ∨ η = -1) {z : Site}
    (hz : z ∈ (frameAt word).freeH) :
    (frameAt word).slip (standardField word) η z = 0 := by
  obtain ⟨hA, hB⟩ := W4NativeSlip.freeH_strip_margin (frameAt word) hz
  apply slip_eq_zero_of_band_word hw hSE
  · omega
  · omega
  · rw [W4NativeSlip.tGrade_add_smul_shortShift]
    rcases hη with rfl | rfl <;> omega
  · rw [W4NativeSlip.tGrade_add_smul_shortShift]
    rcases hη with rfl | rfl <;> omega

/-- **The sign −1 permit with equality on the zero band.** If the four points `c, c − σ, o, o − σ` lie in the t-band, the sign −1 slips of
`o` and `c` are both `0`, so `D₋(o) ≤ D₋(c)` holds with equality. -/
theorem permit_minus_of_band_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {c o : Site}
    (hc1 : 1 - (frameAt word).child.den ≤ (frameAt word).tGrade c)
    (hc2 : (frameAt word).tGrade c ≤ (frameAt word).child.num + 2 * (frameAt word).child.den - 1)
    (hc3 : 1 - (frameAt word).child.den ≤ (frameAt word).tGrade (c + (-1 : ℤ) • (frameAt word).shortShift))
    (hc4 : (frameAt word).tGrade (c + (-1 : ℤ) • (frameAt word).shortShift) ≤
      (frameAt word).child.num + 2 * (frameAt word).child.den - 1)
    (ho1 : 1 - (frameAt word).child.den ≤ (frameAt word).tGrade o)
    (ho2 : (frameAt word).tGrade o ≤ (frameAt word).child.num + 2 * (frameAt word).child.den - 1)
    (ho3 : 1 - (frameAt word).child.den ≤ (frameAt word).tGrade (o + (-1 : ℤ) • (frameAt word).shortShift))
    (ho4 : (frameAt word).tGrade (o + (-1 : ℤ) • (frameAt word).shortShift) ≤
      (frameAt word).child.num + 2 * (frameAt word).child.den - 1) :
    (frameAt word).slip (standardField word) (-1) o ≤ (frameAt word).slip (standardField word) (-1) c := by
  rw [slip_eq_zero_of_band_word hw hSE ho1 ho2 ho3 ho4,
    slip_eq_zero_of_band_word hw hSE hc1 hc2 hc3 hc4]

/-- **The transverse translate of the slip.** The transverse period `F (z + V) = F z + tGrade z + c_V` of the word's standard field
(`StripsM.hper_word`) gives `D_η(z + V) = D_η(z) + 2η` for either sign. -/
theorem slip_add_transverse_word {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (η : ℤ) (z : Site) :
    (frameAt word).slip (standardField word) η (z + (frameAt word).child.modifiedDeck.transverse) =
      (frameAt word).slip (standardField word) η z + 2 * η := by
  have hp := (StripsM.hper_word hw hSE).2
  have e : z + (frameAt word).child.modifiedDeck.transverse + η • (frameAt word).shortShift =
      (z + η • (frameAt word).shortShift) + (frameAt word).child.modifiedDeck.transverse := by
    abel
  have h1 := hp z
  have h2 := hp (z + η • (frameAt word).shortShift)
  have ht := W4NativeSlip.tGrade_add_smul_shortShift (frameAt word) z η
  unfold ChildFrame.slip
  rw [e, h1, h2]
  simp only [Fraction.transverseGrade, ChildFrame.tGrade] at ht ⊢
  linarith

/-- **The slip at a point whose transverse translate back is a free H site.** If `z − V` is free H, `D_η(z) = 2η`. -/
theorem slip_eq_two_of_transverse_freeH {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) {η : ℤ} (hη : η = 1 ∨ η = -1) {z : Site}
    (hz : z - (frameAt word).child.modifiedDeck.transverse ∈ (frameAt word).freeH) :
    (frameAt word).slip (standardField word) η z = 2 * η := by
  have h := slip_add_transverse_word hw hSE η (z - (frameAt word).child.modifiedDeck.transverse)
  rw [sub_add_cancel, slip_eq_zero_freeH_word hw hSE hη hz, zero_add] at h
  exact h

end FLatticePaper.BoundarySlip
