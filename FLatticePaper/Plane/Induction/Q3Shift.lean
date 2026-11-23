import FLatticePaper.Plane.Induction.Q3Inputs

/-! Task 59, step 2 (third Q3 piece): the short shift `σ = shortShift = (2εD, 2εN)` of fix Q3.md, paragraph 4.

* `tGrade σ = −2`: the shift `η σ` moves the transverse grade `t` by `−2η`, as the paragraph says.
* `sGrade σ = 2ε C` with `C = parentC`, and `s_p σ = 2ε T_p`: the parent's `s`-period `T_p` is the shift.
* `t_p σ = 0`: the shift keeps the parent's `t_p`.
* The shifted grades: `t(z + ησ) = t z − 2η`, `t_p(z + ησ) = t_p z`, `s_p(z + ησ) = s_p z + 2 η ε T_p`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

namespace ChildFrame
variable (frame : ChildFrame)

theorem sGrade_shortShift : frame.sGrade frame.shortShift = 2 * frame.eps * frame.parentC := by
  unfold sGrade shortShift parentC
  dsimp only
  ring

theorem parentTGrade_shortShift : frame.parentTGrade frame.shortShift = 0 := by
  unfold parentTGrade shortShift
  dsimp only
  ring

theorem parentSGrade_shortShift :
    frame.parentSGrade frame.shortShift =
      2 * frame.eps * (frame.parents.odd.den * frame.parents.odd.den +
        2 * frame.parents.odd.den * frame.parents.odd.num - frame.parents.odd.num * frame.parents.odd.num) := by
  unfold parentSGrade shortShift
  dsimp only
  ring

/-- The shift `η σ` moves the transverse grade `t` by `−2η`. -/
theorem tGrade_add_shift (z : Site) (η : ℤ) :
    frame.tGrade (z + (η * frame.shortShift.1, η * frame.shortShift.2)) = frame.tGrade z - 2 * η := by
  have key : frame.tGrade (z + (η * frame.shortShift.1, η * frame.shortShift.2)) =
      frame.tGrade z + η * frame.tGrade frame.shortShift := by
    unfold tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  rw [key, frame.tGrade_shortShift]
  ring

/-- The shift `η σ` keeps the parent's transverse grade `t_p`. -/
theorem parentTGrade_add_shift (z : Site) (η : ℤ) :
    frame.parentTGrade (z + (η * frame.shortShift.1, η * frame.shortShift.2)) = frame.parentTGrade z := by
  have key : frame.parentTGrade (z + (η * frame.shortShift.1, η * frame.shortShift.2)) =
      frame.parentTGrade z + η * frame.parentTGrade frame.shortShift := by
    unfold parentTGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  rw [key, frame.parentTGrade_shortShift]
  ring

end ChildFrame

end FLatticePaper.Induction
