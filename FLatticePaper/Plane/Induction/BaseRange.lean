import FLatticePaper.Plane.Induction.Sheets
import FLatticePaper.Plane.Induction.StarFromSheets

/-! The base range `D+(E) ⊂ {0,1,2}` of STRONG_PRICE section 2, with `D = starDiff F σ`, from the arguments of the
archive (task 34, part 3). The inputs are those the B2 audit (section 1) and the STRONG note use:

* the boundary outward directions of the closed polygon `E` (a site of `E` with a neighbour outside `E`);
* `bottomZero`: the pure bottom H arc (outward south only) carries `D = 0` ("D+ and D- vanish on bottom H ... from the
  genuine zero strip");
* `topTwo`: the pure top H arc (outward north only) carries `D = 2` ("on top H they are 2 ... by their V characters");
* `leftRange`: the V arcs (outward west or east, including their corners) carry `D ∈ {0,1,2}` ("the genuine ancestral V
  cut gives D+ in {0,1,2} on left V, hence also on right V");
* `boundaryCover`: every boundary site of `E` is in one of the three cases (a lattice fact about `E`);
* `comparison`: the recurrent comparison principle on the interior of `E` ("apply recurrent comparison to M = F on E,
  against each globally binary shifted/affine competitor"): a range on the boundary of `E` gives a range on `E`.

The conclusion `base` is the range on `E`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- `z` lies in the set `E` and its neighbour in direction `d` lies outside `E`. -/
def OutwardDir (E : Set Site) (d : Site) (z : Site) : Prop := z ∈ E ∧ z + d ∉ E

/-- A site of `E` on the lattice boundary of `E`. -/
def OnBoundary (E : Set Site) (z : Site) : Prop :=
  OutwardDir E (0, 1) z ∨ OutwardDir E (0, -1) z ∨ OutwardDir E (1, 0) z ∨ OutwardDir E (-1, 0) z

/-- The pure bottom H arc: outward south and neither west nor east. -/
def PureBottom (E : Set Site) (z : Site) : Prop :=
  OutwardDir E (0, -1) z ∧ ¬ OutwardDir E (-1, 0) z ∧ ¬ OutwardDir E (1, 0) z

/-- The pure top H arc: outward north and neither west nor east. -/
def PureTop (E : Set Site) (z : Site) : Prop :=
  OutwardDir E (0, 1) z ∧ ¬ OutwardDir E (-1, 0) z ∧ ¬ OutwardDir E (1, 0) z

/-- The V arcs, including the corners: outward west or east. -/
def OnVArc (E : Set Site) (z : Site) : Prop := OutwardDir E (-1, 0) z ∨ OutwardDir E (1, 0) z

/-- The inputs of the base argument. -/
structure BaseInputs (frame : ChildFrame) (F : Field) : Prop where
  bottomZero : ∀ z, PureBottom frame.closedPolygon z →
    starDiff F frame.shortShift z = 0
  topTwo : ∀ z, PureTop frame.closedPolygon z → starDiff F frame.shortShift z = 2
  leftRange : ∀ z, OnVArc frame.closedPolygon z →
    starDiff F frame.shortShift z = 0 ∨ starDiff F frame.shortShift z = 1 ∨ starDiff F frame.shortShift z = 2
  boundaryCover : ∀ z, OnBoundary frame.closedPolygon z →
    PureBottom frame.closedPolygon z ∨ PureTop frame.closedPolygon z ∨ OnVArc frame.closedPolygon z
  comparison : (∀ z, OnBoundary frame.closedPolygon z →
      0 ≤ starDiff F frame.shortShift z ∧ starDiff F frame.shortShift z ≤ 2) →
    ∀ z ∈ frame.closedPolygon, 0 ≤ starDiff F frame.shortShift z ∧ starDiff F frame.shortShift z ≤ 2

/-- The base range of `D` on `E`, from the boundary arcs and the recurrent comparison. -/
theorem base_of_inputs (frame : ChildFrame) {F : Field} (inputs : BaseInputs frame F) :
    ∀ z ∈ frame.closedPolygon, 0 ≤ starDiff F frame.shortShift z ∧ starDiff F frame.shortShift z ≤ 2 := by
  apply inputs.comparison
  intro z hz
  rcases inputs.boundaryCover z hz with h | h | h
  · rw [inputs.bottomZero z h]
    norm_num
  · rw [inputs.topTwo z h]
    norm_num
  · rcases inputs.leftRange z h with h' | h' | h' <;> rw [h'] <;> norm_num

end FLatticePaper.Induction
