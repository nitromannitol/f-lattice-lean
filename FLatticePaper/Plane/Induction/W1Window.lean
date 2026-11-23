import FLatticePaper.Plane.Induction.W1Lower
import FLatticePaper.Plane.Induction.ParentCoordinates
import FLatticePaper.Plane.Induction.ZoneI1

/-! Task 48, step 3: the parent query of the top collar, `x = y − εU − lv` with `lv = (1 − W)(d_q, n_q)`.

The archive (section 2) states `t_p(x) = t_p(y) − W`. Here `t_p(z) = N z₁ − D z₂` is the odd parent's H grade (`parentTGrade`), `U` the
kernel `(d, n)` and `(d_q, n_q)` the even parent, with `d = 2D + d_q`, `n = 2N + n_q` (`child_den_eq`, `child_num_eq`). -/

namespace FLatticePaper.W1Window

open Farey FLatticePaper FLatticePaper.Induction

/-- **The parent query.** `t_p(y − εU − (1 − W)(d_q, n_q)) = t_p(y) − W`. -/
theorem parentTGrade_query (frame : ChildFrame) (y : Site) :
    frame.parentTGrade (y - frame.eps • frame.child.modifiedDeck.kernel -
        (1 - frame.phaseW) • (frame.parents.even.den, frame.parents.even.num)) =
      frame.parentTGrade y - frame.phaseW := by
  rw [frame.child_modifiedDeck_kernel]
  have hden := ZoneI1.child_den_eq frame
  have hnum := ZoneI1.child_num_eq frame
  have he : frame.eps = frame.parents.odd.num * frame.child.den - frame.parents.odd.den * frame.child.num :=
    frame.eps_eq
  unfold ChildFrame.parentTGrade
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_mk, smul_eq_mul]
  rcases frame.eps_unit with h1 | h1
  · have hW : frame.phaseW = 1 := by
      unfold ChildFrame.phaseW
      rw [h1]
      norm_num
    rw [hW, h1]
    rw [h1] at he
    linear_combination he
  · have hW : frame.phaseW = 0 := by
      unfold ChildFrame.phaseW
      rw [h1]
      norm_num
    rw [hW, h1]
    linear_combination frame.parents.odd.num * hden - frame.parents.odd.den * hnum

end FLatticePaper.W1Window
