import FLatticePaper.Plane.Induction.ChartCommon
import FLatticePaper.Plane.Induction.InputExit
import FLatticePaper.Plane.Induction.ExitSlip

/-! # The sign +1 dichotomy at a strictly interior centre (the lower-exit boundary, Q40)

At a strictly interior centre `c` the lower centre exit cannot occur (`centre_not_lower`). Hence, when the two sign +1 common charts both
fail for an edge `o → c` with `c, o ∈ E`, the input exit `InputLowerExit` holds and the window lemmas give `D₊(c) = D₊(o) = 2`
(`plus_chart_or_two`). This is the Q40 boundary claim with no colour hypothesis. -/

namespace FLatticePaper.PlusBoundary

open Farey FLatticePaper FLatticePaper.Induction

/-- A strictly interior centre is not a lower centre exit. -/
theorem centre_not_lower {frame : ChildFrame} {c : Site} (hn3 : 3 ≤ frame.child.num)
    (hnd : frame.child.num + 2 ≤ frame.child.den)
    (hS : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den c) :
    ¬ (frame.tGrade c - 2 < (if EvenSite c then 2 else frame.child.num) - frame.child.periodDenominator) := by
  intro h
  have hT : frame.child.periodDenominator =
      frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := by
    unfold Fraction.periodDenominator
    ring
  obtain ⟨h1, -, -, -⟩ := hS
  unfold FLatticePaper.W1.w1b FLatticePaper.W1.w1T FLatticePaper.W1.w1t at h1
  unfold ChildFrame.tGrade at h
  rw [hT] at h
  split_ifs at h h1 <;> linarith

/-- **The sign +1 dichotomy at a strictly interior centre.** With `c` strictly interior and `c, o ∈ E`, `o` an input of `c`, one of the two
sign +1 common charts holds, or both ends have slip `2` (so the permit is an equality). -/
theorem plus_chart_or_two {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (hn3 : 3 ≤ frame.child.num)
    (hnd : frame.child.num + 2 ≤ frame.child.den) {c o : Site}
    (hS : FLatticePaper.W1.StrictInterior frame.child.num frame.child.den c)
    (hc : c ∈ frame.closedPolygon) (ho : o ∈ frame.closedPolygon) (hEdge : FLatticePaper.Edge o c) :
    (c + frame.shortShift ∈ frame.closedPolygon ∧ o + frame.shortShift ∈ frame.closedPolygon) ∨
      (c - (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num) ∈ frame.closedPolygon ∧
        o - (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num) ∈ frame.closedPolygon) ∨
      (F c - F (c + frame.shortShift) = 2 ∧ F o - F (o + frame.shortShift) = 2) := by
  by_cases hnc : frame.tGrade c - 2 ≥
      (if EvenSite c then 2 else frame.child.num) - frame.child.periodDenominator
  · by_cases hni : frame.tGrade o - 2 ≥
        (if EvenSite o then 2 else frame.child.num) - frame.child.periodDenominator
    · rcases FLatticePaper.Induction.common_chart_option frame hn3 hnd hc ho hEdge hnc hni with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have hex := not_le.mp hni
      have hwin := frame.input_exit_window hc ho hEdge hex hn3 hnd
      exact Or.inr (Or.inr (frame.slip_eq_two_of_window hP hnd hwin))
  · exact absurd (not_le.mp hnc) (centre_not_lower hn3 hnd hS)

end FLatticePaper.PlusBoundary
