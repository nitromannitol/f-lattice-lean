import FLatticePaper.Plane.Induction.Q3Window
import FLatticePaper.Plane.Induction.NoBlackPair
import FLatticePaper.Plane.Induction.ChildNumerator
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.Binary

/-! Task 65, item (3): the exit case of the shifted edge (`hexit`), from the window lemmas `Q3Window` and the packet.

Let `V = (n − d, n + d)` be the child's transverse and `D w = F w − F (w + σ)` (`σ = shortShift`, `η = +1`).

* `slip_translate_V` (packet transverse period): `D w = D (w − V) + 2`, since `tGrade σ = −2` and `transverseGrade = −tGrade`.
* `CentreLowerExit c i`: the centre `c` and its input `i` lie in `E`, and the centre's shifted grade leaves the supported
  interval from below: `t(c) − 2 < a_χ − T` (`a_e = 2`, `a_o = n`).
* `slip_zero_of_centre_exit`: under the window lemma (`Q3Window.lower_exit_*`), the translates `c − V`, `c − V + σ`, `i − V`,
  `i − V + σ` have grades `t + T` and `t + T − 2` in the zero strip, so `F` vanishes there (`HasStrips`); hence `D(c) = D(i) = 2`
  and the slip increment is `0`: the two ends have the same slip. Not a rise.

Named (not closed here): exits of the input `i` itself (the window lemmas take the centre as the exiting end). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The child's transverse `V = (n − d, n + d)`. -/
def ChildFrame.transV (frame : ChildFrame) : Site :=
  (frame.child.num - frame.child.den, frame.child.num + frame.child.den)

theorem ChildFrame.tGrade_add (frame : ChildFrame) (a b : Site) :
    frame.tGrade (a + b) = frame.tGrade a + frame.tGrade b := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem ChildFrame.tGrade_sub_transV (frame : ChildFrame) (w : Site) :
    frame.tGrade (w - frame.transV) = frame.tGrade w + frame.child.periodDenominator := by
  unfold ChildFrame.tGrade ChildFrame.transV Fraction.periodDenominator
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

theorem ChildFrame.tGrade_sub_transV_shift (frame : ChildFrame) (w : Site) :
    frame.tGrade (w - frame.transV + frame.shortShift) =
      frame.tGrade w + frame.child.periodDenominator - 2 := by
  rw [frame.tGrade_add, frame.tGrade_sub_transV, frame.tGrade_shortShift]
  ring

/-- The packet's transverse period, with the transverse grade `−tGrade`: `F(site + V) = F site + tGrade site + c_V`. -/
theorem ChildFrame.periods_transV {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (site : Site) :
    F (site + frame.transV) = F site + frame.tGrade site + frame.coherentConstantV := by
  obtain ⟨-, hV⟩ := hP.periods
  rw [frame.child_modifiedDeck_transverse] at hV
  have h := hV site
  unfold Fraction.transverseGrade at h
  unfold ChildFrame.tGrade ChildFrame.transV
  linarith

/-- The slip translates by the transverse period: `D w = D (w − V) + 2`. -/
theorem ChildFrame.slip_translate_V {F : Field} (frame : ChildFrame) (hP : frame.Packet F) (w : Site) :
    F w - F (w + frame.shortShift) =
      (F (w - frame.transV) - F (w - frame.transV + frame.shortShift)) + 2 := by
  have h1 := frame.periods_transV hP (w - frame.transV)
  have h2 := frame.periods_transV hP (w + frame.shortShift - frame.transV)
  rw [show w - frame.transV + frame.transV = w by abel] at h1
  rw [show w + frame.shortShift - frame.transV + frame.transV = w + frame.shortShift by abel] at h2
  have e : w + frame.shortShift - frame.transV = w - frame.transV + frame.shortShift := by abel
  rw [e] at h2
  have hsh : frame.tGrade (w - frame.transV + frame.shortShift) = frame.tGrade (w - frame.transV) - 2 := by
    rw [frame.tGrade_add, frame.tGrade_shortShift]
    ring
  linarith

/-- An input of an even centre has grade `t ± n`. -/
theorem ChildFrame.tGrade_input_even (frame : ChildFrame) {c i : Site} (he : EvenSite c) (h : Edge i c) :
    frame.tGrade i = frame.tGrade c + frame.child.num ∨ frame.tGrade i = frame.tGrade c - frame.child.num := by
  rcases h with rfl | rfl
  · right
    unfold FLatticePaper.incomingNeg ChildFrame.tGrade
    rw [if_pos he]
    ring
  · left
    unfold FLatticePaper.incomingPos ChildFrame.tGrade
    rw [if_pos he]
    ring

/-- An input of an odd centre has grade `t ± d`. -/
theorem ChildFrame.tGrade_input_odd (frame : ChildFrame) {c i : Site} (ho : ¬ EvenSite c) (h : Edge i c) :
    frame.tGrade i = frame.tGrade c + frame.child.den ∨ frame.tGrade i = frame.tGrade c - frame.child.den := by
  rcases h with rfl | rfl
  · left
    unfold FLatticePaper.incomingNeg ChildFrame.tGrade
    rw [if_neg ho]
    ring
  · right
    unfold FLatticePaper.incomingPos ChildFrame.tGrade
    rw [if_neg ho]
    ring

/-- The parity of an input is opposite to the parity of its centre. -/
theorem evenSite_input_iff {c i : Site} (h : Edge i c) : EvenSite i ↔ ¬ EvenSite c := by
  rcases h with rfl | rfl
  · unfold FLatticePaper.incomingNeg EvenSite
    by_cases he : (c.1 + c.2) % 2 = 0
    · rw [if_pos he]
      simp only
      omega
    · rw [if_neg he]
      simp only
      omega
  · unfold FLatticePaper.incomingPos EvenSite
    by_cases he : (c.1 + c.2) % 2 = 0
    · rw [if_pos he]
      simp only
      omega
    · rw [if_neg he]
      simp only
      omega

/-- The closed polygon at an even site: the even inequalities of `closedPolygon`. -/
theorem ChildFrame.closedPolygon_even {frame : ChildFrame} {z : Site} (he : EvenSite z)
    (hz : z ∈ frame.closedPolygon) :
    2 - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := by
  unfold ChildFrame.closedPolygon at hz
  simp only [Set.mem_setOf_eq, if_pos he] at hz
  exact ⟨hz.1, hz.2.1⟩

/-- The closed polygon at an odd site. -/
theorem ChildFrame.closedPolygon_odd {frame : ChildFrame} {z : Site} (ho : ¬ EvenSite z)
    (hz : z ∈ frame.closedPolygon) :
    frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den := by
  unfold ChildFrame.closedPolygon at hz
  simp only [Set.mem_setOf_eq, if_neg ho] at hz
  exact ⟨hz.1, hz.2.1⟩

/-- A centre of `E` with an input in `E`, whose shifted grade leaves the supported interval from below (`η = +1`): the exit
case of the shifted edge, with the exiting end the centre. -/
def CentreLowerExit (frame : ChildFrame) (c i : Site) : Prop :=
  c ∈ frame.closedPolygon ∧ i ∈ frame.closedPolygon ∧ Edge i c ∧
    frame.tGrade c - 2 < (if EvenSite c then 2 else frame.child.num) - frame.child.periodDenominator

/-- The window conclusions give zero values of `F` at the translates of both ends and of their shifts (zero strip); hence
both ends have slip `2`. -/
theorem ChildFrame.slip_eq_two_of_window {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hnd : frame.child.num + 2 ≤ frame.child.den) {c i : Site}
    (hwin : (2 ≤ frame.tGrade c + frame.child.periodDenominator ∧
        frame.tGrade c + frame.child.periodDenominator ≤ frame.child.num + 1 + frame.child.den ∧
        2 ≤ frame.tGrade i + frame.child.periodDenominator ∧
        frame.tGrade i + frame.child.periodDenominator ≤ frame.child.num + 1 + frame.child.den) ∧
      (1 - frame.child.den ≤ frame.tGrade c - 2 + frame.child.periodDenominator ∧
        frame.tGrade c - 2 + frame.child.periodDenominator ≤ frame.child.num + 2 * frame.child.den - 1 ∧
        1 - frame.child.den ≤ frame.tGrade i - 2 + frame.child.periodDenominator ∧
        frame.tGrade i - 2 + frame.child.periodDenominator ≤ frame.child.num + 2 * frame.child.den - 1)) :
    F c - F (c + frame.shortShift) = 2 ∧ F i - F (i + frame.shortShift) = 2 := by
  obtain ⟨⟨h1, h2, h3, h4⟩, ⟨g1, g2, g3, g4⟩⟩ := hwin
  have hc1 : F (c - frame.transV) = 0 :=
    hP.strips.1 _ (by rw [frame.tGrade_sub_transV]; omega) (by rw [frame.tGrade_sub_transV]; omega)
  have hc2 : F (c - frame.transV + frame.shortShift) = 0 :=
    hP.strips.1 _ (by rw [frame.tGrade_sub_transV_shift]; omega) (by rw [frame.tGrade_sub_transV_shift]; omega)
  have hi1 : F (i - frame.transV) = 0 :=
    hP.strips.1 _ (by rw [frame.tGrade_sub_transV]; omega) (by rw [frame.tGrade_sub_transV]; omega)
  have hi2 : F (i - frame.transV + frame.shortShift) = 0 :=
    hP.strips.1 _ (by rw [frame.tGrade_sub_transV_shift]; omega) (by rw [frame.tGrade_sub_transV_shift]; omega)
  have sc := frame.slip_translate_V hP c
  have si := frame.slip_translate_V hP i
  rw [hc1, hc2] at sc
  rw [hi1, hi2] at si
  constructor <;> linarith

/-- The exit case (`η = +1`, centre exiting from below): the two ends have the same slip, so the slip increment along the
input is `0`, not `1`. -/
theorem ChildFrame.slip_increment_zero_of_centre_exit {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hn : 3 ≤ frame.child.num) (hnd : frame.child.num + 2 ≤ frame.child.den) {c i : Site}
    (hexit : CentreLowerExit frame c i) :
    F i - F (i + frame.shortShift) - (F c - F (c + frame.shortShift)) = 0 := by
  obtain ⟨hc, hi, hEdge, hex⟩ := hexit
  by_cases he : EvenSite c
  · have hz := frame.closedPolygon_even he hc
    have hu := frame.closedPolygon_odd (fun h' => (evenSite_input_iff hEdge).mp h' he) hi
    have hin := frame.tGrade_input_even he hEdge
    rw [if_pos he] at hex
    have hwin := Q3Window.lower_exit_even_end (frame.tGrade c) (frame.tGrade i) frame.child.num frame.child.den
      frame.child.periodDenominator hn hnd hz hu hin hex
    obtain ⟨s1, s2⟩ := frame.slip_eq_two_of_window hP hnd hwin
    linarith
  · have hz := frame.closedPolygon_odd he hc
    have hu := frame.closedPolygon_even ((evenSite_input_iff hEdge).mpr he) hi
    have hin := frame.tGrade_input_odd he hEdge
    rw [if_neg he] at hex
    have hwin := Q3Window.lower_exit_odd_end (frame.tGrade c) (frame.tGrade i) frame.child.num frame.child.den
      frame.child.periodDenominator hn hnd hz hu hin hex
    obtain ⟨s1, s2⟩ := frame.slip_eq_two_of_window hP hnd hwin
    linarith

/-- The exit case is not a rise: the slip increment along the input is `0`. -/
theorem ChildFrame.not_rising_of_centre_exit {F : Field} (frame : ChildFrame) (hP : frame.Packet F)
    (hn : 3 ≤ frame.child.num) (hnd : frame.child.num + 2 ≤ frame.child.den) {c i : Site}
    (hexit : CentreLowerExit frame c i) :
    ¬ RisingBlackPair F frame.shortShift c i := by
  intro hr
  obtain ⟨-, -, -, -, hone⟩ := hr
  have h0 := frame.slip_increment_zero_of_centre_exit hP hn hnd hexit
  simp only [slipIncrement] at hone
  linarith

end FLatticePaper.Induction
