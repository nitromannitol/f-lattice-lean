import FLatticePaper.Plane.Induction.W4Boundary

/-! # The local chain of the free cuts: at most one successor and predecessor

For a free H site `z`, the two candidate successors `z + (1,0)` and `z + (1,1)` cannot both lie in `freeH`: the second
has `z + (1,0)` as its lower neighbour, which lies outside the polygon whenever the first is inside. The same argument
gives the other three cases (H predecessors, V successors, V predecessors). The existence of a successor off the last
site is not proved here: with `T` abstract it fails, so it needs the period identity `T = s(U)`. -/

namespace FLatticePaper.FreeCutSucc

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

theorem mem_freeH_iff (frame : ChildFrame) (z : Site) :
    z ∈ frame.freeH ↔ closedRect frame.child.num frame.child.den z ∧
      ¬ closedRect frame.child.num frame.child.den (z.1, z.2 - 1) ∧
      frame.hSpectrum (frame.tGrade z) := by
  simp only [ChildFrame.freeH, Set.mem_setOf_eq, W1.closedPolygon_eq_closedRect]

theorem mem_freeV_iff (frame : ChildFrame) (z : Site) :
    z ∈ frame.freeV ↔ closedRect frame.child.num frame.child.den z ∧
      ¬ closedRect frame.child.num frame.child.den (z.1 - 1, z.2) ∧
      frame.vSpectrum (frame.sGrade z) := by
  simp only [ChildFrame.freeV, Set.mem_setOf_eq, W1.closedPolygon_eq_closedRect]

/-- The H successor is unique: `z + (1,1) ∈ freeH` forces `z + (1,0) ∉ closedPolygon`. -/
theorem freeH_succ_unique (frame : ChildFrame) {z : Site} (h1 : (z.1 + 1, z.2) ∈ frame.freeH) :
    (z.1 + 1, z.2 + 1) ∉ frame.freeH := by
  intro h2
  rw [mem_freeH_iff] at h1 h2
  simp only [add_sub_cancel_right] at h2
  exact h2.2.1 h1.1

/-- The H predecessor is unique: `z - (1,1) ∈ freeH` forces `z - (1,0)` to be in the polygon, contradicting `z - (1,0) ∈ freeH`. -/
theorem freeH_pred_unique (frame : ChildFrame) {z : Site} (h1 : (z.1 - 1, z.2) ∈ frame.freeH) :
    (z.1 - 1, z.2 - 1) ∉ frame.freeH := by
  intro h2
  rw [mem_freeH_iff] at h1 h2
  exact h1.2.1 h2.1

/-- The V successor is unique: `z + (0,1) ∈ freeV` forces `z + (-1,1)` out of the polygon. -/
theorem freeV_succ_unique (frame : ChildFrame) {z : Site} (h1 : (z.1, z.2 + 1) ∈ frame.freeV) :
    (z.1 - 1, z.2 + 1) ∉ frame.freeV := by
  intro h2
  rw [mem_freeV_iff] at h1 h2
  exact h1.2.1 h2.1

/-- The V predecessor is unique: `z + (1,-1) ∈ freeV` forces `z + (0,-1)` out of the polygon. -/
theorem freeV_pred_unique (frame : ChildFrame) {z : Site} (h1 : (z.1, z.2 - 1) ∈ frame.freeV) :
    (z.1 + 1, z.2 - 1) ∉ frame.freeV := by
  intro h2
  rw [mem_freeV_iff] at h1 h2
  simp only [add_sub_cancel_right] at h2
  exact h2.2.1 h1.1

end FLatticePaper.FreeCutSucc
