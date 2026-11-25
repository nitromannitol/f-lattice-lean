import FLatticePaper.Plane.Induction.ArcRanges
import FLatticePaper.Plane.Induction.BothFreeGrades
import FLatticePaper.Plane.Induction.HFVTip

/-! Task 72 / Q31 step 2, P1: the translated V point lies in the closed polygon.

For a native V point `z ∈ freeV` with the window `2 − c ≤ s(z) ≤ L − 2` and a translation `X` of grade `t(X) = 2`, even parity, and
`c − 2 ≤ s(X) ≤ T − c + 2`, the point `z + X` is in the closed polygon. The grade `t(z)` is in the arc range (`ArcRanges`) for the
interior points; `vFirst` (`t = 0`) and `vLast` (`t = L − T`) are added by their own grades. -/

namespace FLatticePaper.NativeShift

open FLatticePaper FLatticePaper.Induction

/-- **P1.** `z + X` is in the closed polygon. -/
theorem shift_mem_closedPolygon (frame : ChildFrame) {z X : Site} (hz : z ∈ frame.freeV)
    (hsz0 : 2 - (frame.child.den - frame.child.num) ≤ frame.sGrade z)
    (hsz1 : frame.sGrade z ≤ frame.child.den + frame.child.num - 2)
    (hXt : frame.tGrade X = 2) (hXev : EvenSite X)
    (hXs0 : frame.child.den - frame.child.num - 2 ≤ frame.sGrade X)
    (hXs1 : frame.sGrade X ≤ frame.child.periodDenominator - (frame.child.den - frame.child.num) + 2) :
    z + X ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hsum : frame.sGrade (z + X) = frame.sGrade z + frame.sGrade X := by
    unfold ChildFrame.sGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have htsum : frame.tGrade (z + X) = frame.tGrade z + 2 := by
    rw [frame.tGrade_add_pt, hXt]
  have hpar : EvenSite (z + X) ↔ EvenSite z := by
    have := hXev
    unfold EvenSite at this ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hL4 : 4 ≤ frame.child.den + frame.child.num := by omega
  have hT4 : 4 ≤ frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  by_cases he : EvenSite z
  · -- even z: the t-range of z
    have htz : (2 - frame.child.periodDenominator ≤ frame.tGrade z + 2 ∧
        frame.tGrade z + 2 ≤ frame.child.den + frame.child.num - 2) := by
      by_cases h1 : z = vFirst
      · subst h1
        rw [BothFreeGrades.tGrade_vFirst]
        constructor <;> omega
      · by_cases h2 : z = frame.vLast
        · subst h2
          rw [BothFreeGrades.tGrade_vLast]
          constructor <;> omega
        · have := ArcRanges.arc_even_range frame hz he h1 h2
          constructor <;> omega
    unfold ChildFrame.closedPolygon
    rw [Set.mem_setOf_eq]
    by_cases hE : EvenSite (z + X)
    · rw [if_pos hE]
      rw [htsum, hsum]
      refine ⟨by omega, by omega, by omega, by omega⟩
    · exact absurd (hpar.mpr he) hE
  · -- odd z: the t-range of z from `arc_odd_range`
    have hodd : ¬ EvenSite (z + X) := fun h => he (hpar.mp h)
    have htz : frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z + 2 ∧
        frame.tGrade z + 2 ≤ frame.child.den := by
      have := ArcRanges.arc_odd_range frame hz he
      constructor <;> omega
    unfold ChildFrame.closedPolygon
    rw [Set.mem_setOf_eq]
    rw [if_neg hodd]
    rw [htsum, hsum]
    refine ⟨htz.1, htz.2, by omega, by omega⟩

end FLatticePaper.NativeShift
