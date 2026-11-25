import FLatticePaper.Plane.Induction.FreeVWindow
import FLatticePaper.Plane.Induction.FreeEnum
import FLatticePaper.Plane.Induction.BothFreeGrades

/-! Task 72 / Q31 step 2, input 2 (ordinates): the native V points have ordinates in `[0, L − 1]`, and only `vLast` has ordinate `L − 1`.

* `vLast ∈ freeV` (the last point, grades `t = L − T`, `s = 2n`).
* Even `z ∈ freeV`, `z ≠ vLast`: `0 ≤ z₂ ≤ L − 2`, from `T z₂ = n s − L t` with the window and the arc range.
* Odd `z ∈ freeV`: `0 ≤ z₂ ≤ L − 2`; the bound `z₂ ≤ L − 1` is the same identity, and `z₂ = L − 1` is excluded by the uniqueness of the
  free point on ordinate `L − 1` (`CutOnePerOrdinate`), since that point is `vLast`, which is even. -/

namespace FLatticePaper.FreeVOrdinate

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeEnum

/-- The identity `T · z₂ = n s(z) − L t(z)`. -/
theorem T_mul_ordinate (frame : ChildFrame) (z : Site) :
    frame.child.periodDenominator * z.2 =
      frame.child.num * frame.sGrade z - (frame.child.den + frame.child.num) * frame.tGrade z := by
  unfold Fraction.periodDenominator ChildFrame.sGrade ChildFrame.tGrade
  ring

/-- `vLast` is in the free V cut. -/
theorem vLast_mem_freeV (frame : ChildFrame) : frame.vLast ∈ frame.freeV := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  have hT2 : 2 ≤ frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  have he : EvenSite frame.vLast := by
    unfold EvenSite ChildFrame.vLast
    simp only
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [FreeVWindow.mem_closedPolygon_even frame he, BothFreeGrades.tGrade_vLast, FreeVWindow.sGrade_vLast]
    constructor
    · constructor <;> omega
    · constructor <;> omega
  · intro hmem
    have hodd : ¬ EvenSite (frame.vLast.1 - 1, frame.vLast.2) := by
      unfold EvenSite ChildFrame.vLast
      simp only
      omega
    rw [FreeVWindow.mem_closedPolygon_odd frame hodd, FreeVWindow.sGrade_sub_one,
      FreeVWindow.sGrade_vLast] at hmem
    obtain ⟨-, hs1, -⟩ := hmem
    omega
  · unfold ChildFrame.vSpectrum
    rw [FreeVWindow.sGrade_vLast]
    refine ⟨by omega, Or.inl ⟨by omega, le_refl _⟩⟩

/-- **Even ordinates.** An even `z ∈ freeV` has `0 ≤ z₂ ≤ L − 1`, and `z₂ ≤ L − 2` unless `z = vLast`. -/
theorem freeV_even_ordinate (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (he : EvenSite z) :
    0 ≤ z.2 ∧ z.2 ≤ frame.child.den + frame.child.num - 1 ∧
      (z ≠ frame.vLast → z.2 ≤ frame.child.den + frame.child.num - 2) := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨hs0, hs1⟩ := FreeVWindow.freeV_even_window frame hz he
  have hT4 : 4 ≤ frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  by_cases h1 : z = vFirst
  · subst h1
    refine ⟨by simp [vFirst], ?_, fun _ => ?_⟩
    · simp [vFirst]
      omega
    · simp [vFirst]
      omega
  by_cases h2 : z = frame.vLast
  · subst h2
    refine ⟨?_, ?_, fun h => absurd rfl h⟩
    · simp only [ChildFrame.vLast]
      omega
    · simp only [ChildFrame.vLast]
      omega
  have htr := ArcRanges.arc_even_range frame hz he h1 h2
  obtain ⟨ht0, ht1⟩ := htr
  have hid := T_mul_ordinate frame z
  have hTpos : 0 < frame.child.periodDenominator := by omega
  have hlo : 0 ≤ z.2 := by
    by_contra hneg
    have hneg' : z.2 < 0 := not_le.mp hneg
    have : frame.child.periodDenominator * z.2 < 0 := mul_neg_of_pos_of_neg hTpos hneg'
    nlinarith
  have hup : frame.child.periodDenominator * z.2 ≤ frame.child.periodDenominator * (frame.child.den + frame.child.num - 2) := by
    nlinarith
  have hy2 : z.2 ≤ frame.child.den + frame.child.num - 2 := le_of_mul_le_mul_left hup hTpos
  refine ⟨hlo, by omega, fun _ => hy2⟩

/-- **Odd ordinates.** Given the uniqueness of the free point on each ordinate, an odd `z ∈ freeV` has `0 ≤ z₂ ≤ L − 2`. -/
theorem freeV_odd_ordinate (frame : ChildFrame) (hcut : CutOnePerOrdinate frame) {z : Site}
    (hz : z ∈ frame.freeV) (ho : ¬ EvenSite z) :
    0 ≤ z.2 ∧ z.2 ≤ frame.child.den + frame.child.num - 2 := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  obtain ⟨hw0, hw1⟩ := FreeVWindow.freeV_odd_window frame hz ho
  obtain ⟨ht0, ht1⟩ := ArcRanges.arc_odd_range frame hz ho
  have hid := T_mul_ordinate frame z
  have hT2 : 2 ≤ frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  have hTpos : 0 < frame.child.periodDenominator := by omega
  have hTle : frame.child.periodDenominator ≤ 2 * frame.child.den * (frame.child.den + frame.child.num) + 2 * frame.child.num := by
    rw [hT]
    nlinarith
  have hlo : 0 ≤ z.2 := by
    by_contra hneg
    have hneg' : z.2 < 0 := not_le.mp hneg
    have h1 : frame.child.num * (2 - (frame.child.den - frame.child.num)) ≤ frame.child.num * frame.sGrade z :=
      mul_le_mul_of_nonneg_left hw0 (by omega)
    have h2 : frame.child.periodDenominator * z.2 < 0 := mul_neg_of_pos_of_neg hTpos hneg'
    nlinarith
  have hup : frame.child.periodDenominator * z.2 ≤ frame.child.periodDenominator * (frame.child.den + frame.child.num - 1) := by
    have h1 : frame.child.num * frame.sGrade z ≤ frame.child.num * (frame.child.den + frame.child.num - 2) :=
      mul_le_mul_of_nonneg_left hw1 (by omega)
    nlinarith
  have hy1 : z.2 ≤ frame.child.den + frame.child.num - 1 := le_of_mul_le_mul_left hup hTpos
  refine ⟨hlo, ?_⟩
  by_contra hne
  have heq : z.2 = frame.child.den + frame.child.num - 1 := by omega
  have hcutL := hcut (frame.child.den + frame.child.num - 1) (by omega) (by
    unfold FreeEnum.period
    omega)
  obtain ⟨x, -, hxu⟩ := hcutL
  have hzmem : (z.1, frame.child.den + frame.child.num - 1) ∈ frame.freeV := by
    rw [← heq]
    exact hz
  have hv2 : frame.vLast.2 = frame.child.den + frame.child.num - 1 := by
    unfold ChildFrame.vLast
    simp only
    ring
  have hvmem : (frame.vLast.1, frame.child.den + frame.child.num - 1) ∈ frame.freeV := by
    rw [← hv2]
    exact vLast_mem_freeV frame
  have hz1 : z.1 = x := hxu z.1 hzmem
  have hv1 : frame.vLast.1 = x := hxu frame.vLast.1 hvmem
  have hzv : z = frame.vLast := Prod.ext (by rw [hz1, hv1]) (by rw [heq, hv2])
  apply ho
  rw [hzv]
  unfold EvenSite ChildFrame.vLast
  simp only
  omega

end FLatticePaper.FreeVOrdinate
