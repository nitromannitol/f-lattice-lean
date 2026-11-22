import FLatticePaper.Plane.Induction.BaseRange
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.Strips

/-! Geometry of the pure arcs of the closed polygon `E` (task 36).

The pure bottom arc (outward south, neither west nor east) and the pure top arc (outward north, neither west nor east)
are described by the grades `t` and `s` of their sites. Each statement below is linear in the grades, the numerator and
denominator of the child, and the period `T`; the only nonlinear fact used is `2 (d + n) ≤ T`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

namespace ChildFrame

theorem tGrade_addE (frame : ChildFrame) (z : Site) :
    frame.tGrade (z + (1, 0)) = frame.tGrade z + frame.child.num := by
  unfold ChildFrame.tGrade; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem sGrade_addE (frame : ChildFrame) (z : Site) :
    frame.sGrade (z + (1, 0)) = frame.sGrade z + (frame.child.den + frame.child.num) := by
  unfold ChildFrame.sGrade; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem tGrade_addW (frame : ChildFrame) (z : Site) :
    frame.tGrade (z + (-1, 0)) = frame.tGrade z - frame.child.num := by
  unfold ChildFrame.tGrade; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem sGrade_addW (frame : ChildFrame) (z : Site) :
    frame.sGrade (z + (-1, 0)) = frame.sGrade z - (frame.child.den + frame.child.num) := by
  unfold ChildFrame.sGrade; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem tGrade_addN (frame : ChildFrame) (z : Site) :
    frame.tGrade (z + (0, 1)) = frame.tGrade z - frame.child.den := by
  unfold ChildFrame.tGrade; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem sGrade_addN (frame : ChildFrame) (z : Site) :
    frame.sGrade (z + (0, 1)) = frame.sGrade z + (frame.child.den - frame.child.num) := by
  unfold ChildFrame.sGrade; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem tGrade_addS (frame : ChildFrame) (z : Site) :
    frame.tGrade (z + (0, -1)) = frame.tGrade z + frame.child.den := by
  unfold ChildFrame.tGrade; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem sGrade_addS (frame : ChildFrame) (z : Site) :
    frame.sGrade (z + (0, -1)) = frame.sGrade z - (frame.child.den - frame.child.num) := by
  unfold ChildFrame.sGrade; simp only [Prod.fst_add, Prod.snd_add]; ring

theorem evenSite_addE (z : Site) : EvenSite (z + (1, 0)) ↔ ¬ EvenSite z := by
  unfold EvenSite; simp only [Prod.fst_add, Prod.snd_add]; omega

theorem evenSite_addW (z : Site) : EvenSite (z + (-1, 0)) ↔ ¬ EvenSite z := by
  unfold EvenSite; simp only [Prod.fst_add, Prod.snd_add]; omega

theorem evenSite_addN (z : Site) : EvenSite (z + (0, 1)) ↔ ¬ EvenSite z := by
  unfold EvenSite; simp only [Prod.fst_add, Prod.snd_add]; omega

theorem evenSite_addS (z : Site) : EvenSite (z + (0, -1)) ↔ ¬ EvenSite z := by
  unfold EvenSite; simp only [Prod.fst_add, Prod.snd_add]; omega

/-- The period `T` is at least `2 (d + n)`. -/
theorem two_mul_L_le_periodDenominator (frame : ChildFrame) :
    2 * (frame.child.den + frame.child.num) ≤ frame.child.periodDenominator := by
  obtain ⟨hn0, _, hdn, _, hTform⟩ := frame.child_facts
  rw [hTform]
  nlinarith

/-- The sharpened shape of a pure bottom site: its `t` is bounded on the side of its parity. -/
theorem pureBottom_shape (frame : ChildFrame) {z : Site} (hz : PureBottom frame.closedPolygon z) :
    (EvenSite z ∧ 1 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2) ∨
      (¬ EvenSite z ∧ frame.child.num - 1 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den) := by
  obtain ⟨hn0, hnd, hdn, hd3, hTform⟩ := frame.child_facts
  have hT2 := frame.two_mul_L_le_periodDenominator
  unfold PureBottom OutwardDir at hz
  obtain ⟨⟨hzE, hS⟩, hW, hE⟩ := hz
  have hWin : z + (-1, 0) ∈ frame.closedPolygon := by
    by_contra h; exact hW ⟨hzE, h⟩
  have hEin : z + (1, 0) ∈ frame.closedPolygon := by
    by_contra h; exact hE ⟨hzE, h⟩
  rw [frame.mem_closedPolygon_iff] at hzE hWin hEin
  rw [frame.mem_closedPolygon_iff, frame.tGrade_addS, frame.sGrade_addS, evenSite_addS] at hS
  rw [frame.tGrade_addW, frame.sGrade_addW, evenSite_addW] at hWin
  rw [frame.tGrade_addE, frame.sGrade_addE, evenSite_addE] at hEin
  unfold EvenSite at *
  omega

/-- The sharpened shape of a pure top site, shifted by the transverse period `T`. -/
theorem pureTop_shape (frame : ChildFrame) {z : Site} (hz : PureTop frame.closedPolygon z) :
    (EvenSite z ∧ frame.tGrade z + frame.child.periodDenominator ≤ frame.child.den + frame.child.num - 1 ∧
        2 ≤ frame.tGrade z + frame.child.periodDenominator) ∨
      (¬ EvenSite z ∧ frame.tGrade z + frame.child.periodDenominator ≤ frame.child.den + 1 ∧
        frame.child.num ≤ frame.tGrade z + frame.child.periodDenominator) := by
  obtain ⟨hn0, hnd, hdn, hd3, hTform⟩ := frame.child_facts
  have hT2 := frame.two_mul_L_le_periodDenominator
  unfold PureTop OutwardDir at hz
  obtain ⟨⟨hzE, hN⟩, hW, hE⟩ := hz
  have hWin : z + (-1, 0) ∈ frame.closedPolygon := by
    by_contra h; exact hW ⟨hzE, h⟩
  have hEin : z + (1, 0) ∈ frame.closedPolygon := by
    by_contra h; exact hE ⟨hzE, h⟩
  rw [frame.mem_closedPolygon_iff] at hzE hWin hEin
  rw [frame.mem_closedPolygon_iff, frame.tGrade_addN, frame.sGrade_addN, evenSite_addN] at hN
  rw [frame.tGrade_addW, frame.sGrade_addW, evenSite_addW] at hWin
  rw [frame.tGrade_addE, frame.sGrade_addE, evenSite_addE] at hEin
  unfold EvenSite at *
  omega

/-- The modified transverse deck is `(n − d, n + d)`. -/
theorem modTransverse_eq (frame : ChildFrame) :
    frame.child.modifiedDeck.transverse = (frame.child.num - frame.child.den, frame.child.num + frame.child.den) := by
  simp [Fraction.modifiedDeck, Fraction.unmodifiedDeck]

/-- Translating by the transverse deck `z − V` raises the `t`-grade by the period `T`. -/
theorem tGrade_sub_modTransverse (frame : ChildFrame) (z : Site) :
    frame.tGrade (z - frame.child.modifiedDeck.transverse) =
      frame.tGrade z + frame.child.periodDenominator := by
  rw [frame.modTransverse_eq]
  unfold ChildFrame.tGrade Fraction.periodDenominator
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- The `t`-range of a pure bottom site: the strip of `F`'s zero arc. -/
theorem pureBottom_strip (frame : ChildFrame) {z : Site} (hz : PureBottom frame.closedPolygon z) :
    3 - frame.child.den ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1 := by
  obtain ⟨hn0, hnd, hdn, hd3, _⟩ := frame.child_facts
  rcases frame.pureBottom_shape hz with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> constructor <;> omega

/-- The `t`-range of the pure top site after the transverse shift `z − V`: again the zero strip. -/
theorem pureTop_strip (frame : ChildFrame) {z : Site} (hz : PureTop frame.closedPolygon z) :
    3 - frame.child.den ≤ frame.tGrade z + frame.child.periodDenominator ∧
      frame.tGrade z + frame.child.periodDenominator ≤ frame.child.num + 2 * frame.child.den - 1 := by
  obtain ⟨hn0, hnd, hdn, hd3, _⟩ := frame.child_facts
  rcases frame.pureTop_shape hz with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> constructor <;> omega

/-- A site cannot be both on the pure bottom arc and on the pure top arc. -/
theorem not_pureBottom_and_pureTop (frame : ChildFrame) {z : Site}
    (hb : PureBottom frame.closedPolygon z) (ht : PureTop frame.closedPolygon z) : False := by
  obtain ⟨hn0, hnd, hdn, hd3, _⟩ := frame.child_facts
  have hT2 := frame.two_mul_L_le_periodDenominator
  rcases frame.pureBottom_shape hb with ⟨_, h1, _⟩ | ⟨_, h1, _⟩ <;>
    rcases frame.pureTop_shape ht with ⟨_, h2, _⟩ | ⟨_, h2, _⟩ <;> unfold EvenSite at * <;> omega

end ChildFrame

/-- The cover of the boundary of `E` by the three arcs: a site with an outward west or east neighbour is on a V arc;
otherwise it is outward south (pure bottom) or outward north (pure top). -/
theorem onBoundary_cover (E : Set Site) {z : Site} (hz : OnBoundary E z) :
    PureBottom E z ∨ PureTop E z ∨ OnVArc E z := by
  unfold OnBoundary OnVArc PureBottom PureTop at *
  rcases hz with hN | hS | hE | hW
  · by_cases hWE : OutwardDir E (-1, 0) z ∨ OutwardDir E (1, 0) z
    · exact Or.inr (Or.inr hWE)
    · exact Or.inr (Or.inl ⟨hN, (not_or.mp hWE).1, (not_or.mp hWE).2⟩)
  · by_cases hWE : OutwardDir E (-1, 0) z ∨ OutwardDir E (1, 0) z
    · exact Or.inr (Or.inr hWE)
    · exact Or.inl ⟨hS, (not_or.mp hWE).1, (not_or.mp hWE).2⟩
  · exact Or.inr (Or.inr (Or.inr hE))
  · exact Or.inr (Or.inr (Or.inl hW))

end FLatticePaper.Induction
