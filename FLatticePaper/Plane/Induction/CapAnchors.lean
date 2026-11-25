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

/-- The s-grade of the odd anchor: `s(2−k, k−1) = d + 3n − 2nk`. -/
theorem sGrade_anchor_odd (frame : ChildFrame) (k : ℤ) :
    frame.sGrade (2 - k, k - 1) = frame.child.den + 3 * frame.child.num - 2 * frame.child.num * k := by
  unfold ChildFrame.sGrade
  ring

/-- **The odd harmonic anchor value.** `F(2−k, k−1) = m(k)` when the anchor is in the harmonic strip, by `HasStrips`. -/
theorem anchor_value_odd {frame : ChildFrame} {F : Field} (hS : frame.HasStrips F) (k : ℤ)
    (hlo : 1 - 2 * frame.child.den ≤ frame.child.den + 3 * frame.child.num - 2 * frame.child.num * k)
    (hhi : frame.child.den + 3 * frame.child.num - 2 * frame.child.num * k ≤ 2 * (frame.child.den + frame.child.num) - 1) :
    F (2 - k, k - 1) = FLatticePaper.QuadraticCap.capMin k := by
  have hs : 1 - 2 * frame.child.den ≤ frame.sGrade (2 - k, k - 1) ∧
      frame.sGrade (2 - k, k - 1) ≤ 2 * (frame.child.den + frame.child.num) - 1 := by
    rw [sGrade_anchor_odd]
    exact ⟨hlo, hhi⟩
  rw [hS.2 (2 - k, k - 1) hs.1 hs.2]
  exact FLatticePaper.CapRecursion.harmonicGrid_anchor_odd k

/-- **The sheet monotonicity of the cap, even sheet** (ALL_SLOPE_STEP, "B_j ≤ m(j)" through the even harmonic anchor; the note's
"monotonicity in increasing negative t on each sheet", from the preceding period, strip and signed comparison bounds). Named: no lemma of
the repository gives it (`W1NonfreeHsq.psi_mono` is the monotonicity of the sheet potential Ψ along retained edges, not of the field in
t). Numerically true on the replay's scalar field (`scripts/w1_sheet_mono.py`: 0 violations over 14 proper entries). The zero-strip values
`B_0, B_1, A_0, A_1` are obtained from `zero_value` without it. -/
def SheetMono (frame : ChildFrame) (F : Field) : Prop :=
  ∀ u v : Site, EvenSite u → EvenSite v → frame.tGrade u ≤ frame.tGrade v → frame.tGrade v ≤ 0 → F u ≤ F v

/-- **The sheet monotonicity, odd sheet** (ALL_SLOPE_STEP, the odd anchors `A_k ≥ m(k)` for `k ≥ ⌈u⌉+1`: the odd anchor has smaller
t-grade than the ray site). Named for the same reason as `SheetMono`; numerically true on the replay's scalar field (0 violations). -/
def SheetMonoOdd (frame : ChildFrame) (F : Field) : Prop :=
  ∀ u v : Site, ¬ EvenSite u → ¬ EvenSite v → frame.tGrade u ≤ frame.tGrade v → frame.tGrade v ≤ 0 → F u ≤ F v

end FLatticePaper.CapAnchors
