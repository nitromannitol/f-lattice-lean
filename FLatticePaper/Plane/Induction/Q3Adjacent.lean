import FLatticePaper.Plane.Induction.ParentCoordinates

/-! Task 59, step 2 (paragraph 5, the adjacent primary chart): the parent grade of `−e`.

With the even parent `n_q/d_q`, its kernel `U_q = (d_q, n_q)`, its transverse `V_q = (n_q − d_q, n_q + d_q)`, and
`e = V_q + ε U_q`, the odd parent's H grade satisfies
  `t_p(−e) = D (d_q + n_q) + N (d_q − n_q) − 1`
(fix Q3.md paragraph 5; checked numerically on words of length ≤ 4). The identity uses `ε = N d_q − n_q D` and `ε² = 1`.

The shift identity `p(x) = c₀ − P′(Zx)` with the shift `ε U_q` is in `Q3Bridge.lean` (`paragraph5_field_identity`),
proved from the codebase's `quarterTurnField_sub_shift` and the `U_p`-periodicity, with the lattice bridge as a hypothesis. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

namespace ChildFrame
variable (frame : ChildFrame)

/-- The even parent's kernel `U_q = (d_q, n_q)`. -/
def evenKernel : Site := (frame.parents.even.den, frame.parents.even.num)

/-- The even parent's transverse `V_q = (n_q − d_q, n_q + d_q)`. -/
def evenTransverse : Site := (frame.parents.even.num - frame.parents.even.den, frame.parents.even.num + frame.parents.even.den)

/-- `e = V_q + ε U_q`. -/
def sheetStep : Site :=
  (frame.evenTransverse.1 + frame.eps * frame.evenKernel.1, frame.evenTransverse.2 + frame.eps * frame.evenKernel.2)

theorem eps_det_even : frame.parents.odd.num * frame.parents.even.den -
    frame.parents.even.num * frame.parents.odd.den = frame.eps := by
  unfold ChildFrame.eps Fraction.det
  ring

theorem parentTGrade_neg_sheetStep :
    frame.parentTGrade (-frame.sheetStep) =
      frame.parents.odd.den * (frame.parents.even.den + frame.parents.even.num) +
        frame.parents.odd.num * (frame.parents.even.den - frame.parents.even.num) - 1 := by
  have hε2 : frame.eps * frame.eps = 1 := by
    rcases frame.eps_unit with h | h <;> rw [h] <;> norm_num
  have hdet := frame.eps_det_even
  unfold parentTGrade sheetStep evenTransverse evenKernel
  simp only [Prod.fst_neg, Prod.snd_neg]
  linear_combination (-frame.eps) * hdet + (-1 : ℤ) * hε2

end ChildFrame

end FLatticePaper.Induction
