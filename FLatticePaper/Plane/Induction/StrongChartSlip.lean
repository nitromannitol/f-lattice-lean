import FLatticePaper.Plane.Induction.ChartCommon

/-! Task 70 (c): the slip chart dichotomy for an edge with both ends in `E`: the wiring of the slip chart to `ChartCommon.common_chart_option`. -/

namespace FLatticePaper.StrongChartSlip

open Farey FLatticePaper FLatticePaper.Induction

/-- **(c) The slip chart dichotomy.** For an edge `i → c` with both ends in `E` (and the `t`-support of `common_chart_option`), the ends are
shifted together into `E` by `σ` or by `−ε(dq, nq)`. -/
theorem slip_chart_dichotomy (frame : ChildFrame) (hn3 : 3 ≤ frame.child.num)
    (hnd : frame.child.num + 2 ≤ frame.child.den) {c i : Site}
    (hc : c ∈ frame.closedPolygon) (hi : i ∈ frame.closedPolygon) (hEdge : Edge i c)
    (hnc : frame.tGrade c - 2 ≥ (if EvenSite c then 2 else frame.child.num) - frame.child.periodDenominator)
    (hni : frame.tGrade i - 2 ≥ (if EvenSite i then 2 else frame.child.num) - frame.child.periodDenominator) :
    (c + frame.shortShift ∈ frame.closedPolygon ∧ i + frame.shortShift ∈ frame.closedPolygon) ∨
      (c - (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num) ∈ frame.closedPolygon ∧
        i - (frame.eps * frame.parents.even.den, frame.eps * frame.parents.even.num) ∈ frame.closedPolygon) :=
  common_chart_option frame hn3 hnd hc hi hEdge hnc hni

end FLatticePaper.StrongChartSlip
