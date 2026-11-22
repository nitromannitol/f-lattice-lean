import FLatticePaper.Plane.Induction.StarFromSheets

/-! The star estimates S1 and S2 of the sewn standard field, from the local inputs of the archive's range argument
(task 32). With `D = F − F(· + σ)` (`σ = shortShift`):

* `rangeE`: `D ∈ {0,1,2}` on the closed polygon `E` (STRONG_PRICE section 2: `D+(E) ⊂ {0,1,2}`);
* `rangeIn`: `D ∈ {0,1,2}` at the inputs of the sites of `E` (the same range on the physical inputs, section 3:
  "All these statements concern both physical inputs");
* `unitJump`: on every edge `u → e` with `e ∈ E`, `|D u − D e| ≤ 1` (section 3: "an edge jump of two impossible").

The unit jump excludes the edge `0 — 2`, which is the hypothesis `hJ` of `star_of_closedPolygon`; the cover of the
plane by translates of `E` and the deck invariance of `D` then give `HasUnitSlip` (S1) and `NoEvenSlipSaddle` (S2). -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

/-- The three local inputs of the range argument for `D = starDiff F σ` on the closed polygon. -/
structure StarRangeInputs (frame : ChildFrame) (F : Field) : Prop where
  rangeE : ∀ e ∈ frame.closedPolygon, starDiff F frame.shortShift e = 0 ∨ starDiff F frame.shortShift e = 1 ∨
    starDiff F frame.shortShift e = 2
  rangeIn : ∀ e ∈ frame.closedPolygon, ∀ u, Edge u e →
    starDiff F frame.shortShift u = 0 ∨ starDiff F frame.shortShift u = 1 ∨ starDiff F frame.shortShift u = 2
  unitJump : ∀ e ∈ frame.closedPolygon, ∀ u, Edge u e →
    -1 ≤ starDiff F frame.shortShift u - starDiff F frame.shortShift e ∧
      starDiff F frame.shortShift u - starDiff F frame.shortShift e ≤ 1

/-- A unit jump excludes the edge between the values `0` and `2`. -/
theorem not_zero_two_of_unit_jump {x y : ℤ} (h : -1 ≤ x - y ∧ x - y ≤ 1) :
    ¬((y = 0 ∧ x = 2) ∨ (y = 2 ∧ x = 0)) := by
  omega

/-- The star estimates S1 (unit slip) and S2 (no even slip saddle) of the sewn standard field, from the range inputs
of the archive, with the deck covering of `E` (`star_of_closedPolygon`). -/
theorem starRange_S1S2_of_inputs (frame : ChildFrame) {F : Field} {cU cV : ℤ}
    (hper : HasGeneratorPeriods frame.child F cU cV) (inputs : StarRangeInputs frame F) :
    HasUnitSlip F (fun z => F (z + frame.shortShift)) ∧
      NoEvenSlipSaddle F (fun z => F (z + frame.shortShift)) := by
  refine frame.star_of_closedPolygon hper inputs.rangeE inputs.rangeIn ?_
  intro e he u hu hbad
  rcases hbad with ⟨h0, h2⟩ | ⟨h2, h0⟩
  · exact not_zero_two_of_unit_jump (inputs.unitJump e he u hu) (Or.inl ⟨h0, h2⟩)
  · exact not_zero_two_of_unit_jump (inputs.unitJump e he u hu) (Or.inr ⟨h2, h0⟩)

end FLatticePaper.Induction
