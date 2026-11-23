import FLatticePaper.Plane.Induction.ParentCoordinates
import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! Task 59, step 2 (part): the exceptional values of the odd parent's web (W1 constructor, sections 3–4).

In the parent's own coordinates (`t_p = N x₁ − D x₂`, `s_p = (D+N) x₁ + (D−N) x₂`, `ε = N d − D n`):
* the special sites `H_0 = (1,0)` and `V_0 = (0,0)` have `t_p = N`, `s_p = D + N` and `s_p = 0`;
* the top odd H site `H_{d−1} = (d, n−1)` has `t_p = D + ε`, so it leaves the odd range `[N, D]` exactly when `ε = +1`;
* the top even V site `V_{L−1} = (n−d+1, n+d−1)` has `s_p = 2N − 2ε`, so it leaves `[0, 2N]` exactly when `ε = −1`;
* the native even H endpoints `(2l − b, b)` have `t_p = 2Nl − L_p b`, and the native odd V endpoints `(−b, 2l − 1 − b)`
  have `s_p = 2f − (D − N)` with `f = (D−N) l − D b`; these are the identities behind the residue exceptions. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

namespace ChildFrame
variable (frame : ChildFrame)

theorem parentTGrade_hFirst : frame.parentTGrade hFirst = frame.parents.odd.num := by
  unfold parentTGrade hFirst
  dsimp only
  ring

theorem parentSGrade_hFirst : frame.parentSGrade hFirst = frame.parents.odd.den + frame.parents.odd.num := by
  unfold parentSGrade hFirst
  dsimp only
  ring

theorem parentSGrade_vFirst : frame.parentSGrade vFirst = 0 := by
  unfold parentSGrade vFirst
  dsimp only
  ring

theorem parentTGrade_hLast : frame.parentTGrade frame.hLast = frame.parents.odd.den + frame.eps := by
  unfold parentTGrade hLast
  rw [frame.eps_eq]
  dsimp only
  ring

theorem parentSGrade_vLast : frame.parentSGrade frame.vLast = 2 * frame.parents.odd.num - 2 * frame.eps := by
  unfold parentSGrade vLast
  rw [frame.eps_eq]
  dsimp only
  ring

/-- `H_{d-1}` leaves the odd range `[N, D]` (from above) exactly when `ε = +1`. -/
theorem parentTGrade_hLast_gt_iff :
    frame.parents.odd.den < frame.parentTGrade frame.hLast ↔ frame.eps = 1 := by
  rw [frame.parentTGrade_hLast]
  rcases frame.eps_unit with h | h <;> rw [h] <;> constructor <;> intro hh <;> omega

/-- `V_{L-1}` leaves the even range `[0, 2N]` (from above) exactly when `ε = −1`. -/
theorem parentSGrade_vLast_gt_iff :
    2 * frame.parents.odd.num < frame.parentSGrade frame.vLast ↔ frame.eps = -1 := by
  rw [frame.parentSGrade_vLast]
  rcases frame.eps_unit with h | h <;> rw [h] <;> constructor <;> intro hh <;> omega

theorem parentTGrade_even_endpoint (l b : ℤ) :
    frame.parentTGrade (2 * l - b, b) =
      2 * frame.parents.odd.num * l - (frame.parents.odd.den + frame.parents.odd.num) * b := by
  unfold parentTGrade
  dsimp only
  ring

theorem parentSGrade_odd_endpoint (l b : ℤ) :
    frame.parentSGrade (-b, 2 * l - 1 - b) =
      2 * ((frame.parents.odd.den - frame.parents.odd.num) * l - frame.parents.odd.den * b) -
        (frame.parents.odd.den - frame.parents.odd.num) := by
  unfold parentSGrade
  dsimp only
  ring

end ChildFrame

end FLatticePaper.Induction
