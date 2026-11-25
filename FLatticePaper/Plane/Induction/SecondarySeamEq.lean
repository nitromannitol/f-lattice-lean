import FLatticePaper.Plane.Induction.SlipReflect
import FLatticePaper.Plane.Induction.StrongHStrip

/-! The closed secondary equalities of STRONG §2 (the bottom exit and its reflected top, SECONDARY_SEAMS).

* **Bottom.** At the two `t`-levels of the secondary bottom, `n − 2` (the input `z`) and `L − 2` (the even endpoint `u`), the
  short slip vanishes: `D₋ = 0`. This is the zero band of the short slip (`StrongHStrip.slip_eq_zero_of_tBand`), which needs
  only `3 − d ≤ t ≤ n + 2d − 3`, true at both levels when `3 ≤ n` and `n + 2 ≤ d`.
* **Reflected top.** The reflection `R z = centre − z` gives `D₊(R z) = D₋(z) + 2` (`slip_reflect`), so `D₋ = 0` at the bottom
  point forces `D₊ = 2` at its reflected top image. -/

namespace FLatticePaper.SecondarySeamEq

open Farey FLatticePaper FLatticePaper.Induction

/-- **The bottom exit: `D₋ = 0`** at the two secondary bottom levels `t = n − 2` and `t = L − 2`. -/
theorem slipMinus_zero_of_bottom (frame : ChildFrame) (F : Field) (hS : frame.HasStrips F)
    (hn3 : 3 ≤ frame.child.num) (hnd : frame.child.num + 2 ≤ frame.child.den) {z : Site}
    (ht : frame.tGrade z = frame.child.num - 2 ∨ frame.tGrade z = frame.child.den + frame.child.num - 2) :
    frame.slip F (-1) z = 0 := by
  refine FLatticePaper.StrongHStrip.slip_eq_zero_of_tBand frame F hS (η := -1) (Or.inr rfl) z ?_ ?_
  · rcases ht with h | h <;> omega
  · rcases ht with h | h <;> omega

/-- **The reflection of the slip.** `D₊` at the reflected point `centre − z` is `D₋` at `z`, plus two. -/
theorem slipPlus_centre_eq (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (z : Site) :
    frame.slip F 1 (frame.centre - z) = frame.slip F (-1) z + 2 := by
  have h := frame.slip_reflect hP (frame.centre - z)
  rw [sub_sub_cancel] at h
  unfold ChildFrame.slip
  rw [one_smul, neg_one_smul]
  linarith [h]

/-- **The reflected top: `D₊ = 2`.** If `D₋` vanishes at `z`, then `D₊` at the reflected point `centre − z` equals `2`. -/
theorem slipPlus_centre_eq_two (frame : ChildFrame) {F : Field} (hP : frame.Packet F) {z : Site}
    (hz : frame.slip F (-1) z = 0) : frame.slip F 1 (frame.centre - z) = 2 := by
  rw [slipPlus_centre_eq frame hP z, hz]
  norm_num

/-- **The secondary bottom and its reflected top together.** At a point `z` on either bottom level, `D₋ z = 0` and the
reflected point `centre − z` has `D₊ = 2`. -/
theorem secondary_bottom_top (frame : ChildFrame) {F : Field} (hP : frame.Packet F) (hS : frame.HasStrips F)
    (hn3 : 3 ≤ frame.child.num) (hnd : frame.child.num + 2 ≤ frame.child.den) {z : Site}
    (ht : frame.tGrade z = frame.child.num - 2 ∨ frame.tGrade z = frame.child.den + frame.child.num - 2) :
    frame.slip F (-1) z = 0 ∧ frame.slip F 1 (frame.centre - z) = 2 :=
  ⟨slipMinus_zero_of_bottom frame F hS hn3 hnd ht,
    slipPlus_centre_eq_two frame hP (slipMinus_zero_of_bottom frame F hS hn3 hnd ht)⟩

end FLatticePaper.SecondarySeamEq
