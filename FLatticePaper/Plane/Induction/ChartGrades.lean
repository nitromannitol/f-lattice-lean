import FLatticePaper.Plane.Induction.InputExit
import FLatticePaper.Plane.Induction.Q3Para10
import FLatticePaper.Plane.Induction.Binary

/-! Task 66 (2)(c) plumbing: the grades of the shifted points and their translates, the membership of a point in the closed
polygon from its grades, and the `C`-bounds `0 ≤ 2C ≤ T`, with `C = D L + N (d − n)` (`s(σ) = 2 ε C`, `s(U_p) = 2C`). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- `C = D L + N (d − n)`: `s(U_p) = 2C` and `s(σ) = 2 ε C`. -/
def ChildFrame.Cconst (frame : ChildFrame) : ℤ :=
  frame.parents.odd.den * (frame.child.den + frame.child.num) +
    frame.parents.odd.num * (frame.child.den - frame.child.num)

theorem ChildFrame.sGrade_child_kernel (frame : ChildFrame) :
    frame.sGrade (frame.child.den, frame.child.num) = frame.child.periodDenominator := by
  unfold ChildFrame.sGrade Fraction.periodDenominator
  ring

theorem ChildFrame.tGrade_child_kernel (frame : ChildFrame) :
    frame.tGrade (frame.child.den, frame.child.num) = 0 := by
  unfold ChildFrame.tGrade
  ring

theorem ChildFrame.sGrade_shortShift_val (frame : ChildFrame) :
    frame.sGrade frame.shortShift = 2 * frame.eps * frame.Cconst := by
  unfold ChildFrame.sGrade ChildFrame.shortShift ChildFrame.Cconst
  ring

theorem ChildFrame.sGrade_even (frame : ChildFrame) (z : Site) : frame.sGrade z % 2 = 0 := by
  obtain ⟨hn, hd⟩ := frame.child_odd
  have hL : (frame.child.den + frame.child.num) % 2 = 0 := by omega
  have hD : (frame.child.den - frame.child.num) % 2 = 0 := by omega
  unfold ChildFrame.sGrade
  have h1 : ((frame.child.den + frame.child.num) * z.1) % 2 = 0 := by
    rw [Int.mul_emod, hL]
    simp
  have h2 : ((frame.child.den - frame.child.num) * z.2) % 2 = 0 := by
    rw [Int.mul_emod, hD]
    simp
  rw [Int.add_emod, h1, h2]
  norm_num

/-- The input step of `s`: `s(i) = s(c) ± L` at an even centre, `s(c) ± (d − n)` at an odd one. -/
theorem ChildFrame.sGrade_input_even (frame : ChildFrame) {c i : Site} (he : EvenSite c) (h : Edge i c) :
    frame.sGrade i = frame.sGrade c + (frame.child.den + frame.child.num) ∨
      frame.sGrade i = frame.sGrade c - (frame.child.den + frame.child.num) := by
  rcases h with rfl | rfl
  · right
    unfold FLatticePaper.incomingNeg ChildFrame.sGrade
    rw [if_pos he]
    ring
  · left
    unfold FLatticePaper.incomingPos ChildFrame.sGrade
    rw [if_pos he]
    ring

theorem ChildFrame.sGrade_input_odd (frame : ChildFrame) {c i : Site} (ho : ¬ EvenSite c) (h : Edge i c) :
    frame.sGrade i = frame.sGrade c + (frame.child.den - frame.child.num) ∨
      frame.sGrade i = frame.sGrade c - (frame.child.den - frame.child.num) := by
  rcases h with rfl | rfl
  · right
    unfold FLatticePaper.incomingNeg ChildFrame.sGrade
    rw [if_neg ho]
    ring
  · left
    unfold FLatticePaper.incomingPos ChildFrame.sGrade
    rw [if_neg ho]
    ring

/-- A point with the grades of an even site in the closed polygon's even window lies in the closed polygon. -/
theorem ChildFrame.mem_closedPolygon_of_even {frame : ChildFrame} {p : Site} (he : EvenSite p)
    (h1 : 2 - frame.child.periodDenominator ≤ frame.tGrade p ∧ frame.tGrade p ≤ frame.child.den + frame.child.num - 2)
    (h2 : 0 ≤ frame.sGrade p ∧ frame.sGrade p ≤ frame.child.periodDenominator + 2 * frame.child.num) :
    p ∈ frame.closedPolygon := by
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq, if_pos he]
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

theorem ChildFrame.mem_closedPolygon_of_odd {frame : ChildFrame} {p : Site} (ho : ¬ EvenSite p)
    (h1 : frame.child.num - frame.child.periodDenominator ≤ frame.tGrade p ∧ frame.tGrade p ≤ frame.child.den)
    (h2 : 2 - frame.child.den + frame.child.num ≤ frame.sGrade p ∧
      frame.sGrade p ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) :
    p ∈ frame.closedPolygon := by
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq, if_neg ho]
  exact ⟨h1.1, h1.2, h2.1, h2.2⟩

/-- The `C`-bounds: `0 ≤ 2C ≤ T` (`T − 2C = s(U_q) = L u + (d − n) v ≥ 0`). -/
theorem ChildFrame.Cconst_bounds (frame : ChildFrame) :
    0 ≤ 2 * frame.Cconst ∧ 2 * frame.Cconst ≤ frame.child.periodDenominator := by
  obtain ⟨hd, hn, -⟩ := frame.linear_facts
  obtain ⟨hD, hN0, hND⟩ := frame.valid.odd_bounds
  obtain ⟨hq, hn0, hnq⟩ := frame.valid.even_bounds
  have hTC : frame.child.periodDenominator - 2 * frame.Cconst =
      (frame.child.den + frame.child.num) * frame.parents.even.den +
        (frame.child.den - frame.child.num) * frame.parents.even.num := by
    unfold Fraction.periodDenominator ChildFrame.Cconst
    rw [hd, hn]
    ring
  have hLpos : 0 ≤ frame.child.den + frame.child.num := by omega
  have hDpos : 0 ≤ frame.child.den - frame.child.num := by omega
  constructor
  · unfold ChildFrame.Cconst
    rw [hd, hn]
    nlinarith
  · nlinarith

end FLatticePaper.Induction
