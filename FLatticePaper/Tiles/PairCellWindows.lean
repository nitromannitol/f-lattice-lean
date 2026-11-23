import FLatticePaper.Tiles.PairCellForms

/-! Task 53, item 2 (covering reduction), section 3: the window functionals of the parents on the child's cell.

A child cell point is `z = B0 + u U + v V` with `B0 = (1/2, −1/2)`, `U = μ X`, `V = V(X)`, `X = mP + Q`, `μ = 2` (odd child,
`m = 1`) or `μ = 1` (even child, `m = 2`). The functionals of a parent are affine in `(u, v)`:
`t_R(z) = t_R(B0) + u t_R(U) + v t_R(V)` and likewise for `s_R`. This section records the values of these coefficients,
which are the inputs of the window inequalities. -/

namespace FLatticePaper.Tiles.PairCellWindows

open FLatticePaper.Tiles.PairCellForms

/-- The point `B0 + u U + v V` in site coordinates. -/
def cellPt (u v : ℚ) (U V : ℚ × ℚ) : ℚ × ℚ := (1 / 2 + u * U.1 + v * V.1, -1 / 2 + u * U.2 + v * V.2)

/-- `t` at a cell point: `t(B0) + u t(U) + v t(V)` with `t(B0) = (n + d)/2`. -/
theorem tq_cellPt (n d u v : ℚ) (U V : ℚ × ℚ) :
    PairCellForms.tq n d (cellPt u v U V) = (n + d) / 2 + u * PairCellForms.tq n d U + v * PairCellForms.tq n d V := by
  simp only [PairCellForms.tq, cellPt]
  ring

/-- `s` at a cell point: `s(B0) + u s(U) + v s(V)` with `s(B0) = n`. -/
theorem sq_cellPt (n d u v : ℚ) (U V : ℚ × ℚ) :
    PairCellForms.sq n d (cellPt u v U V) = n + u * PairCellForms.sq n d U + v * PairCellForms.sq n d V := by
  simp only [PairCellForms.sq, cellPt]
  ring

/-- `s_P(X) = m T_P + s_P(Q)`. -/
theorem sq_Xv (m dP nP dQ nQ : ℚ) :
    PairCellForms.sq nP dP (PairCellForms.Xv m dP nP dQ nQ) = m * PairCellForms.Tq nP dP + PairCellForms.sq nP dP (dQ, nQ) := by
  simp only [PairCellForms.sq, PairCellForms.Xv, PairCellForms.Tq]
  ring

/-- `s_P(V_P) = 0`. -/
theorem sq_VP (dP nP : ℚ) : PairCellForms.sq nP dP (PairCellForms.Vv (dP, nP)) = 0 := by
  simp only [PairCellForms.sq, PairCellForms.Vv]
  ring

/-- `s_P(V_Q) = 2δ`, with `δ = dP nQ − nP dQ`. -/
theorem sq_VQ (dP nP dQ nQ : ℚ) : PairCellForms.sq nP dP (PairCellForms.Vv (dQ, nQ)) = 2 * (dP * nQ - nP * dQ) := by
  simp only [PairCellForms.sq, PairCellForms.Vv]
  ring

/-- `t_Q(X) = mδ`. -/
theorem tq_Q_Xv (m dP nP dQ nQ : ℚ) : PairCellForms.tq nQ dQ (PairCellForms.Xv m dP nP dQ nQ) = m * (dP * nQ - nP * dQ) := by
  simp only [PairCellForms.tq, PairCellForms.Xv]
  ring

/-- `t_Q(V_X) = −(m s_Q(P) + T_Q)`. -/
theorem tq_Q_VX (m dP nP dQ nQ : ℚ) :
    PairCellForms.tq nQ dQ (PairCellForms.Vv (PairCellForms.Xv m dP nP dQ nQ)) = -(m * PairCellForms.sq nQ dQ (dP, nP) + PairCellForms.Tq nQ dQ) := by
  simp only [PairCellForms.tq, PairCellForms.Vv, PairCellForms.Xv, PairCellForms.sq, PairCellForms.Tq]
  ring

end FLatticePaper.Tiles.PairCellWindows
