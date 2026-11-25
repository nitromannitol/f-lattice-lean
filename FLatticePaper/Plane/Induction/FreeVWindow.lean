import FLatticePaper.Plane.Induction.ArcRanges
import FLatticePaper.Plane.Induction.BothFreeGrades
import FLatticePaper.Plane.Induction.VArcLongitudinal

/-! Task 72 / Q31 step 2, input 1: the native V window from `freeV`.

For `z ∈ freeV` (closed polygon, exit `(z₁ − 1, z₂) ∉ E`, V spectrum):
* even `z`: `0 ≤ s(z) ≤ 2n`;
* odd `z`: `2 − c ≤ s(z) ≤ L − 2`.
The lower bounds are the polygon's. The upper bounds use the exit: the left neighbour `z − (1, 0)` has `s − L` and `t − n`. Its
parity is opposite, so the polygon test on it fails only in `s`; the arc `t`-ranges (`ArcRanges`) make the `t`-test hold. `s` is
always even (`sGrade_mod_two`), and `L` is even (`child_odd`). The exceptional points `vFirst` (`s = 0`) and `vLast` (`s = 2n`) are
checked directly. -/

namespace FLatticePaper.FreeVWindow

open FLatticePaper FLatticePaper.Induction

/-- The shifted grades: `t(z − (1, 0)) = t(z) − n` and `s(z − (1, 0)) = s(z) − L`. -/
theorem tGrade_sub_one (frame : ChildFrame) (z : Site) :
    frame.tGrade (z.1 - 1, z.2) = frame.tGrade z - frame.child.num := by
  unfold ChildFrame.tGrade
  ring

theorem sGrade_sub_one (frame : ChildFrame) (z : Site) :
    frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
  unfold ChildFrame.sGrade
  ring

/-- `vLast` has `s = 2n`. -/
theorem sGrade_vLast (frame : ChildFrame) : frame.sGrade frame.vLast = 2 * frame.child.num := by
  unfold ChildFrame.sGrade ChildFrame.vLast
  ring

/-- `vFirst` has `s = 0`. -/
theorem sGrade_vFirst (frame : ChildFrame) : frame.sGrade vFirst = 0 := by
  unfold ChildFrame.sGrade vFirst
  ring

/-- Unfolding the closed polygon at an even site. -/
theorem mem_closedPolygon_even (frame : ChildFrame) {w : Site} (he : EvenSite w) :
    w ∈ frame.closedPolygon ↔
      (2 - frame.child.periodDenominator ≤ frame.tGrade w ∧ frame.tGrade w ≤ frame.child.den + frame.child.num - 2) ∧
        (0 ≤ frame.sGrade w ∧ frame.sGrade w ≤ frame.child.periodDenominator + 2 * frame.child.num) := by
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq]
  rw [if_pos he]
  tauto

/-- Unfolding the closed polygon at an odd site. -/
theorem mem_closedPolygon_odd (frame : ChildFrame) {w : Site} (ho : ¬ EvenSite w) :
    w ∈ frame.closedPolygon ↔
      (frame.child.num - frame.child.periodDenominator ≤ frame.tGrade w ∧ frame.tGrade w ≤ frame.child.den) ∧
        (2 - frame.child.den + frame.child.num ≤ frame.sGrade w ∧
          frame.sGrade w ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2) := by
  unfold ChildFrame.closedPolygon
  simp only [Set.mem_setOf_eq]
  rw [if_neg ho]
  tauto

/-- **The even window.** For an even `z ∈ freeV`, `0 ≤ s(z) ≤ 2n`. -/
theorem freeV_even_window (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (he : EvenSite z) :
    0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * frame.child.num := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hs2 := frame.sGrade_mod_two z
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  have hCP : z ∈ frame.closedPolygon := hz.1
  have hexit : (z.1 - 1, z.2) ∉ frame.closedPolygon := hz.2.1
  obtain ⟨⟨ht0, ht1⟩, ⟨hs0, hs1⟩⟩ := (mem_closedPolygon_even frame he).mp hCP
  refine ⟨hs0, ?_⟩
  by_cases h1 : z = vFirst
  · subst h1
    rw [sGrade_vFirst]
    omega
  by_cases h2 : z = frame.vLast
  · subst h2
    rw [sGrade_vLast]
  have htr := ArcRanges.arc_even_range frame hz he h1 h2
  by_contra hgt
  apply hexit
  have hodd : ¬ EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at he ⊢
    simp only at he ⊢
    omega
  rw [mem_closedPolygon_odd frame hodd, tGrade_sub_one, sGrade_sub_one]
  constructor
  · constructor <;> omega
  · constructor <;> omega

/-- **The odd window.** For an odd `z ∈ freeV`, `2 − c ≤ s(z) ≤ L − 2`. -/
theorem freeV_odd_window (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (ho : ¬ EvenSite z) :
    2 - (frame.child.den - frame.child.num) ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.den + frame.child.num - 2 := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hs2 := frame.sGrade_mod_two z
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  have hCP : z ∈ frame.closedPolygon := hz.1
  have hexit : (z.1 - 1, z.2) ∉ frame.closedPolygon := hz.2.1
  obtain ⟨⟨ht0, ht1⟩, ⟨hs0, hs1⟩⟩ := (mem_closedPolygon_odd frame ho).mp hCP
  refine ⟨by omega, ?_⟩
  by_contra hgt
  have htr := ArcRanges.arc_odd_range frame hz ho
  apply hexit
  have heven : EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at ho ⊢
    simp only at ho ⊢
    omega
  rw [mem_closedPolygon_even frame heven, tGrade_sub_one, sGrade_sub_one]
  constructor
  · constructor <;> omega
  · constructor <;> omega

end FLatticePaper.FreeVWindow
