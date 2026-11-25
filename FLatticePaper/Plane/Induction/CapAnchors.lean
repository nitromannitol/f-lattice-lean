import FLatticePaper.Plane.Induction.CapRecursion
import FLatticePaper.Plane.Induction.Binary

/-! The strip values of the all-slope cap (ALL_SLOPE_STEP, "The uniform quadratic cap").

The strips are the packet's (`ChildFrame.HasStrips`): `F = 0` where the t-grade is in the zero strip, and `F = h0` where the s-grade is in
the harmonic strip. The even harmonic anchor `z_j = (1−j, j−1)` has s-grade `2n(1−j)`, so it lies in the harmonic strip for `2n(j−1) ≤ 2d−1`,
and there `F z_j = h0 z_j = m(j)` (`harmonicGrid_anchor`). The only named input of the cap is the sheet monotonicity, which compares an even
site with an anchor of greater t-grade (`SheetMono`). -/

namespace FLatticePaper.CapAnchors

open FLatticePaper FLatticePaper.Induction

/-- **The zero strip value.** `F = 0` at every site whose t-grade lies in the zero strip (`HasStrips`). -/
theorem zero_value {frame : ChildFrame} {F : Field} (hS : frame.HasStrips F) {z : Site}
    (h1 : 1 - frame.child.den ≤ frame.tGrade z) (h2 : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1) :
    F z = 0 :=
  hS.1 z h1 h2

/-- The s-grade of the even harmonic anchor: `s(1−j, j−1) = 2n(1−j)`. -/
theorem sGrade_anchor (frame : ChildFrame) (j : ℤ) :
    frame.sGrade (1 - j, j - 1) = 2 * frame.child.num * (1 - j) := by
  unfold ChildFrame.sGrade
  ring

/-- **The harmonic anchor value.** `F(1−j, j−1) = m(j)` when the anchor is in the harmonic strip (`2n(j−1) ≤ 2d − 1`), by `HasStrips`. -/
theorem anchor_value {frame : ChildFrame} {F : Field} (hS : frame.HasStrips F) (j : ℤ)
    (hlo : 1 - 2 * frame.child.den ≤ 2 * frame.child.num * (1 - j))
    (hhi : 2 * frame.child.num * (1 - j) ≤ 2 * (frame.child.den + frame.child.num) - 1) :
    F (1 - j, j - 1) = FLatticePaper.QuadraticCap.capMin j := by
  have hs : 1 - 2 * frame.child.den ≤ frame.sGrade (1 - j, j - 1) ∧
      frame.sGrade (1 - j, j - 1) ≤ 2 * (frame.child.den + frame.child.num) - 1 := by
    rw [sGrade_anchor]
    exact ⟨hlo, hhi⟩
  rw [hS.2 (1 - j, j - 1) hs.1 hs.2]
  exact FLatticePaper.CapRecursion.harmonicGrid_anchor j

/-- **The sheet monotonicity of the cap** (ALL_SLOPE_STEP, "B_j ≤ m(j)" through the even anchor): on the even sheet, the field does not
decrease from a site of smaller t-grade to a site of greater t-grade in the negative range. This is the named input of the cap; the zero
strip values `B_0, B_1, A_0, A_1` are obtained from `zero_value` without it. -/
def SheetMono (frame : ChildFrame) (F : Field) : Prop :=
  ∀ u v : Site, EvenSite u → EvenSite v → frame.tGrade u ≤ frame.tGrade v → frame.tGrade v ≤ 0 → F u ≤ F v

end FLatticePaper.CapAnchors
