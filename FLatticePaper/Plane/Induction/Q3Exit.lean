import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! Task 59, step 2, paragraph 2: the exit lemma from the parity rectangle (PROVISIONAL; the two hypotheses are named).

The open parity rectangle `E°` (W1_CONSTRUCTOR section 1, task 45) is, with `L = d + n` and `T` the child period:
* even sites: `L − 2 − T < t < 2` and `2n < s < T`;
* odd sites:  `d − T < t < n` and `L − 2 < s < T + 2 − d + n`.

Named hypotheses, to be replaced by W1's theorem when it lands (checked numerically on words of length ≤ 4 by
`scripts/q3_rect_check.py`):
* `hRectInputs`: a point of the open rectangle has both of its inputs in the closed polygon `E`;
* `hBoundary`: a point of `E` outside the open rectangle lies on a boundary spectrum, i.e. `t` or `s` is in the H or
  V spectrum up to a shift by `±T`.

Exit lemma: a centre of `E` with an input outside `E` lies on a boundary spectrum. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

namespace ChildFrame
variable (frame : ChildFrame)

/-- The open parity rectangle of W1 (PROVISIONAL reading of task 45). -/
def openRect (z : Site) : Prop :=
  if EvenSite z then
    frame.child.den + frame.child.num - 2 - frame.child.periodDenominator < frame.tGrade z ∧
      frame.tGrade z < 2 ∧ 2 * frame.child.num < frame.sGrade z ∧
      frame.sGrade z < frame.child.periodDenominator
  else
    frame.child.den - frame.child.periodDenominator < frame.tGrade z ∧ frame.tGrade z < frame.child.num ∧
      frame.child.den + frame.child.num - 2 < frame.sGrade z ∧
      frame.sGrade z < frame.child.periodDenominator + 2 - frame.child.den + frame.child.num

/-- `z` lies on a boundary spectrum: `t` or `s` is in the H or V spectrum up to a shift by `±T` (PROVISIONAL). -/
def onBoundarySpectrum (z : Site) : Prop :=
  ∃ k : ℤ, (k = -1 ∨ k = 0 ∨ k = 1) ∧
    (frame.hSpectrum (frame.tGrade z + k * frame.child.periodDenominator) ∨
      frame.vSpectrum (frame.sGrade z + k * frame.child.periodDenominator))

/-- Exit lemma (paragraph 2): a centre of `E` with an input outside `E` lies on a boundary spectrum, given the two
named hypotheses. -/
theorem exit_centre_on_boundary_spectrum
    (hRectInputs : ∀ z : Site, frame.openRect z → ∀ i : Site, (i = incomingNeg z ∨ i = incomingPos z) →
      i ∈ frame.closedPolygon)
    (hBoundary : ∀ z : Site, z ∈ frame.closedPolygon → ¬ frame.openRect z → frame.onBoundarySpectrum z)
    (z i : Site) (hz : z ∈ frame.closedPolygon) (hi : i = incomingNeg z ∨ i = incomingPos z)
    (hout : i ∉ frame.closedPolygon) : frame.onBoundarySpectrum z := by
  by_contra hb
  have hrect : frame.openRect z := by
    by_contra hr
    exact hb (hBoundary z hz hr)
  exact hout (hRectInputs z hrect i hi)

end ChildFrame

end FLatticePaper.Induction
