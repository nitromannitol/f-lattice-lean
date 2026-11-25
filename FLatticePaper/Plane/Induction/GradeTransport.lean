import FLatticePaper.Plane.Induction.ParentCoordinates
import FLatticePaper.Plane.Induction.ConjFreeRoot
import FLatticePaper.Plane.Induction.W1Phase

/-! # The grade transport between the physical child and the conjugate child (the boundary calculus of Q33)

For the odd parent `(N, D)` of a child frame with child `(n, d)`, `T = d² + 2dn − n²` (the child period), `T_p = D² + 2DN − N²`
(the odd parent's period), `C = D(d+n) + N(d−n)` and `ε` the determinant, the identity `C² − 2ε² = T_p · T` holds, and the
forward transform `T · t_p = C t + ε s`, `T · s_p = C s + 2ε t` inverts to
`T_p · t = C t_p − ε s_p`, `T_p · s = C s_p − 2ε t_p`.

Composed with the conjugate grades at `zTurn x` (`conj_tGrade_zTurn`, `conj_sGrade_zTurn`), this expresses the physical child grades of
`lv + zTurnInv q` by the conjugate grades of `q`: the strict conditions of the two charts are linear conditions on the parent grades of
`zTurnInv q`. -/

namespace FLatticePaper.GradeTransport

open Farey FLatticePaper FLatticePaper.Induction

/-- `C² − 2ε² = T_p · T` for a child frame. -/
theorem parentC_sq_sub (frame : ChildFrame) :
    frame.parentC ^ 2 - 2 * frame.eps ^ 2 =
      FLatticePaper.Induction.oddParentPeriod frame * frame.child.periodDenominator := by
  unfold FLatticePaper.Induction.oddParentPeriod ChildFrame.parentC Fraction.periodDenominator
  rw [frame.eps_eq]
  ring

/-- The child period is positive. -/
theorem periodDenominator_pos (frame : ChildFrame) : 0 < frame.child.periodDenominator := by
  obtain ⟨h1, h2, h3, h4, -⟩ := frame.child_facts
  unfold Fraction.periodDenominator
  nlinarith

/-- **The inverse transform of the H grade**: `T_p · t(z) = C · t_p(z) − ε · s_p(z)`. -/
theorem oddPeriod_mul_tGrade (frame : ChildFrame) (z : Site) :
    FLatticePaper.Induction.oddParentPeriod frame * frame.tGrade z =
      frame.parentC * frame.parentTGrade z - frame.eps * frame.parentSGrade z := by
  have hT := periodDenominator_pos frame
  have hTne : frame.child.periodDenominator ≠ 0 := ne_of_gt hT
  have h1 := ChildFrame.periodDenominator_parentTGrade frame z
  have h2 := ChildFrame.periodDenominator_parentSGrade frame z
  have hid := parentC_sq_sub frame
  apply mul_left_cancel₀ hTne
  linear_combination (-frame.parentC) * h1 + frame.eps * h2 - frame.tGrade z * hid

/-- **The inverse transform of the S grade**: `T_p · s(z) = C · s_p(z) − 2ε · t_p(z)`. -/
theorem oddPeriod_mul_sGrade (frame : ChildFrame) (z : Site) :
    FLatticePaper.Induction.oddParentPeriod frame * frame.sGrade z =
      frame.parentC * frame.parentSGrade z - 2 * frame.eps * frame.parentTGrade z := by
  have hT := periodDenominator_pos frame
  have hTne : frame.child.periodDenominator ≠ 0 := ne_of_gt hT
  have h1 := ChildFrame.periodDenominator_parentTGrade frame z
  have h2 := ChildFrame.periodDenominator_parentSGrade frame z
  have hid := parentC_sq_sub frame
  apply mul_left_cancel₀ hTne
  linear_combination (2 * frame.eps) * h1 - frame.parentC * h2 - frame.sGrade z * hid

/-- The parent grades of `zTurnInv q`, and the conjugate grades at `q`: `t_c(q) = L_p − s_p(x)`, `s_c(q) = 2 (t_p(x) − n_p)` for
`x = zTurnInv q` (the conjugate child is the rotated odd parent, so its grades are the parent's grades at `zTurn x`). -/
theorem conj_grades_of_zTurnInv {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (q : Site) :
    (frameAt (conjWord word)).tGrade q = (frameAt word).parents.odd.den + (frameAt word).parents.odd.num -
        (frameAt word).parentSGrade (W1Phase.zTurnInv q) ∧
      (frameAt (conjWord word)).sGrade q =
        2 * ((frameAt word).parentTGrade (W1Phase.zTurnInv q) - (frameAt word).parents.odd.num) := by
  have hz : zTurn (W1Phase.zTurnInv q) = q := by
    simp only [zTurn, W1Phase.zTurnInv]
    ext <;> simp
  constructor
  · have := conj_tGrade_zTurn h (W1Phase.zTurnInv q)
    rw [hz] at this
    exact this
  · have := conj_sGrade_zTurn h (W1Phase.zTurnInv q)
    rw [hz] at this
    exact this

end FLatticePaper.GradeTransport
