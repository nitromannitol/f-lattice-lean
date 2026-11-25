import FLatticePaper.Plane.Induction.ClippedCore
import FLatticePaper.Plane.Induction.SheetOffsets
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.Binary

/-! Task 72 / Q31 step 2, the arithmetic of the translations `X` used by the clipped identity and the child strip (P5).

With `U_p = (2D, 2N)` and `U_q = (d_q, n_q)`:
* `t(U_p) = −2ε` and `t(U_q) = 2ε` (so `t(X) = 2` in each phase);
* `s(U_p) ≥ c − 2` and `s(U_q) ≥ c − 2`, and `s(U_p) + s(U_q) = T`;
* the child strip `F = h0` on `1 − 2d ≤ s ≤ 2(d + n) − 1` (`HasStrips`, the packet of the word's own field). -/

namespace FLatticePaper.ClippedArith

open Farey FLatticePaper FLatticePaper.Induction

theorem eps_det (frame : ChildFrame) :
    frame.eps = frame.parents.odd.num * frame.parents.even.den - frame.parents.odd.den * frame.parents.even.num := by
  unfold ChildFrame.eps Fraction.det
  ring

/-- `t(U_p) = −2ε`, with `t(U_p) = 2` in phase 0 (ε = −1). -/
theorem tGrade_Upar (frame : ChildFrame) :
    frame.tGrade (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) = -2 * frame.eps := by
  unfold ChildFrame.tGrade
  rw [eps_det frame, ZoneI1.child_num_eq frame, ZoneI1.child_den_eq frame]
  ring

/-- `t(U_q) = 2ε`, with `t(U_q) = 2` in phase 1 (ε = 1). -/
theorem tGrade_Uq (frame : ChildFrame) :
    frame.tGrade (frame.parents.even.den, frame.parents.even.num) = 2 * frame.eps := by
  unfold ChildFrame.tGrade
  rw [eps_det frame, ZoneI1.child_num_eq frame, ZoneI1.child_den_eq frame]
  ring

/-- `s(U_p) + s(U_q) = T`. -/
theorem sGrade_sum (frame : ChildFrame) :
    frame.sGrade (2 * frame.parents.odd.den, 2 * frame.parents.odd.num)
      + frame.sGrade (frame.parents.even.den, frame.parents.even.num) = frame.child.periodDenominator := by
  unfold ChildFrame.sGrade
  rw [ZoneI1.child_num_eq frame, ZoneI1.child_den_eq frame]
  unfold Fraction.periodDenominator
  rw [ZoneI1.child_num_eq frame, ZoneI1.child_den_eq frame]
  ring

/-- `s(U_p) ≥ c − 2`. -/
theorem sGrade_Upar_ge (frame : ChildFrame) :
    frame.child.den - frame.child.num - 2 ≤
      frame.sGrade (2 * frame.parents.odd.den, 2 * frame.parents.odd.num) := by
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := frame.child_facts
  obtain ⟨hDpos, hN0, -⟩ := frame.valid.odd_bounds
  unfold ChildFrame.sGrade
  simp only
  nlinarith

/-- `s(U_q) ≥ c − 2`. -/
theorem sGrade_Uq_ge (frame : ChildFrame) :
    frame.child.den - frame.child.num - 2 ≤
      frame.sGrade (frame.parents.even.den, frame.parents.even.num) := by
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := frame.child_facts
  obtain ⟨hdq, hnq, -⟩ := frame.valid.even_bounds
  unfold ChildFrame.sGrade
  simp only
  nlinarith

/-- **The child strip (P5):** `F = h0` on the child's `s`-strip `1 − 2d ≤ s ≤ 2(d + n) − 1`. -/
theorem child_strip {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (z : Site)
    (hs0 : 1 - 2 * frame.child.den ≤ frame.sGrade z)
    (hs1 : frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1) :
    F z = harmonicGrid z :=
  hP.strips.2 z hs0 hs1

end FLatticePaper.ClippedArith
