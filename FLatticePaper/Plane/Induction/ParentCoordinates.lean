import FLatticePaper.Plane.Induction.ChildFrame

/-! Task 59, step 2 (part): the exact parent coordinates of a child frame (W1 constructor, section 1).

With `L = d + n`, `T = d² + 2dn − n²`, `C = D L + N (d − n)` and `ε = N d − D n`, the odd parent's grades of a physical
site `z` are `t_p = (C t + ε s)/T` and `s_p = (C s + 2ε t)/T`. In the parent's own coordinates these are
`t_p = N x₁ − D x₂` and `s_p = (D+N) x₁ + (D−N) x₂`. The identities below are the arithmetic of that transform:
they are polynomial identities, proved from `eps_eq` and the unfolded period. -/

namespace FLatticePaper.Induction

open Farey

namespace ChildFrame
variable (frame : ChildFrame)

/-- The scalar `C = D L + N (d − n)` of the exact coordinate transform. -/
def parentC : ℤ :=
  frame.parents.odd.den * (frame.child.den + frame.child.num) +
    frame.parents.odd.num * (frame.child.den - frame.child.num)

/-- The odd parent's H grade `t_p(x) = N x₁ − D x₂` in its own coordinates. -/
def parentTGrade (x : Site) : ℤ := frame.parents.odd.num * x.1 - frame.parents.odd.den * x.2

theorem periodDenominator_parentTGrade (z : Site) :
    frame.child.periodDenominator * frame.parentTGrade z =
      frame.parentC * frame.tGrade z + frame.eps * frame.sGrade z := by
  unfold parentTGrade parentC tGrade sGrade Fraction.periodDenominator
  rw [frame.eps_eq]
  ring

theorem periodDenominator_parentSGrade (z : Site) :
    frame.child.periodDenominator * frame.parentSGrade z =
      frame.parentC * frame.sGrade z + 2 * frame.eps * frame.tGrade z := by
  unfold parentSGrade parentC tGrade sGrade Fraction.periodDenominator
  rw [frame.eps_eq]
  ring

theorem parentC_mul_num :
    frame.parentC * frame.child.num =
      frame.parents.odd.num * frame.child.periodDenominator -
        frame.eps * (frame.child.den + frame.child.num) := by
  unfold parentC Fraction.periodDenominator
  rw [frame.eps_eq]
  ring

theorem parentC_mul_den :
    frame.parentC * frame.child.den =
      frame.parents.odd.den * frame.child.periodDenominator +
        frame.eps * (frame.child.den - frame.child.num) := by
  unfold parentC Fraction.periodDenominator
  rw [frame.eps_eq]
  ring

theorem parentC_mul_L :
    frame.parentC * (frame.child.den + frame.child.num) =
      (frame.parents.odd.den + frame.parents.odd.num) * frame.child.periodDenominator -
        2 * frame.eps * frame.child.num := by
  unfold parentC Fraction.periodDenominator
  rw [frame.eps_eq]
  ring

end ChildFrame

end FLatticePaper.Induction
