import FLatticePaper.Plane.Induction.ExitSlip

/-! Task 66 (3'): the input as the exiting end (the parity table of `Q3Window` with the roles of the centre and its input
exchanged). For `c, i ∈ E` with `i` an input of `c`, the input's shifted grade `t(i) − 2` leaves the supported interval from
below (`t(i) − 2 < a_χ(i) − T`, `a = 2` at an even site and `a = n` at an odd one). The window bounds of the zero-strip
argument (`slip_eq_two_of_window`) are linear consequences of the `E` bounds, the input step `t(c) = t(i) ± n` (`c` even) or
`t(c) = t(i) ± d` (`c` odd), and the exit condition. So the input exit is not a rise. -/

namespace FLatticePaper.Induction

/-- The input exit: `c, i ∈ E`, `i` an input of `c`, and the input's shifted grade leaves the supported interval from below. -/
def InputLowerExit (frame : ChildFrame) (c i : Site) : Prop :=
  c ∈ frame.closedPolygon ∧ i ∈ frame.closedPolygon ∧ Edge i c ∧
    frame.tGrade i - 2 < (if EvenSite i then 2 else frame.child.num) - frame.child.periodDenominator

/-- The window bounds of the input exit (the exiting end is the input). -/
theorem ChildFrame.input_exit_window (frame : ChildFrame) {c i : Site} (hc : c ∈ frame.closedPolygon)
    (hi : i ∈ frame.closedPolygon) (hEdge : Edge i c)
    (hex : frame.tGrade i - 2 < (if EvenSite i then 2 else frame.child.num) - frame.child.periodDenominator)
    (hn3 : 3 ≤ frame.child.num) (hnd : frame.child.num + 2 ≤ frame.child.den) :
    (2 ≤ frame.tGrade c + frame.child.periodDenominator ∧
        frame.tGrade c + frame.child.periodDenominator ≤ frame.child.num + 1 + frame.child.den ∧
        2 ≤ frame.tGrade i + frame.child.periodDenominator ∧
        frame.tGrade i + frame.child.periodDenominator ≤ frame.child.num + 1 + frame.child.den) ∧
      (1 - frame.child.den ≤ frame.tGrade c - 2 + frame.child.periodDenominator ∧
        frame.tGrade c - 2 + frame.child.periodDenominator ≤ frame.child.num + 2 * frame.child.den - 1 ∧
        1 - frame.child.den ≤ frame.tGrade i - 2 + frame.child.periodDenominator ∧
        frame.tGrade i - 2 + frame.child.periodDenominator ≤ frame.child.num + 2 * frame.child.den - 1) := by
  have hpar : (frame.child.den + frame.child.num) % 2 = 0 := by
    obtain ⟨-, -, -, -, -, -, -, -, hp⟩ := frame.linear_facts
    omega
  by_cases he : EvenSite i
  · -- the input is even, so the centre is odd: t(c) = t(i) ± d
    rw [if_pos he] at hex
    have hco : ¬ EvenSite c := fun h' => (evenSite_input_iff hEdge).mp he h'
    have hcpu := hc
    have hipu := hi
    have hcE := frame.closedPolygon_odd hco hcpu
    have hiE := frame.closedPolygon_even he hipu
    have hin := frame.tGrade_input_odd hco hEdge
    obtain ⟨hc1, hc2⟩ := hcE
    obtain ⟨hi1, hi2⟩ := hiE
    rcases hin with hin | hin <;> omega
  · -- the input is odd, so the centre is even: t(c) = t(i) ± n
    rw [if_neg he] at hex
    have hce : EvenSite c := by
      by_contra h'
      exact he ((evenSite_input_iff hEdge).mpr h')
    have hcE := frame.closedPolygon_even hce hc
    have hiE := frame.closedPolygon_odd he hi
    have hin := frame.tGrade_input_even hce hEdge
    obtain ⟨hc1, hc2⟩ := hcE
    obtain ⟨hi1, hi2⟩ := hiE
    rcases hin with hin | hin <;> omega

/-- The input exit: the two ends have slip `2`, so the slip increment is `0`, not `1`. -/
theorem ChildFrame.slip_increment_zero_of_input_exit {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hn3 : 3 ≤ frame.child.num) (hnd : frame.child.num + 2 ≤ frame.child.den) {c i : Site}
    (hexit : InputLowerExit frame c i) :
    F i - F (i + frame.shortShift) - (F c - F (c + frame.shortShift)) = 0 := by
  obtain ⟨hc, hi, hEdge, hex⟩ := hexit
  have hwin := frame.input_exit_window hc hi hEdge hex hn3 hnd
  obtain ⟨s1, s2⟩ := frame.slip_eq_two_of_window hP hnd hwin
  linarith

end FLatticePaper.Induction
