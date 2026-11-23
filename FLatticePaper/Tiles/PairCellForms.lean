import FLatticePaper.Tiles.PairNominal

/-! Task 53, item 2 (covering reduction), section 2: the window functionals of a parent on the child's periods.

A fraction `(n, d)` (num, den) has the window functionals `t(v) = n v₁ − d v₂` and `s(v) = (d + n) v₁ + (d − n) v₂` (the
`tCo`, `sCo` of the window). For a parent `P = (d_P, n_P)` and `Q = (d_Q, n_Q)` the child vector is `X = mP + Q`, and the
grouped periods are `U_X = μ X` and `V_X = V(X) = mV_P + V_Q`, with `V(d,n) = (n − d, d + n)`.

The identities below are the ones used in the cell reduction (the note's `t_P(U_X) = −gδ`, `t_P(V_X) = −(mS + K)`,
`S = T_P`, `K = s_P(Q)`). -/

namespace FLatticePaper.Tiles.PairCellForms

/-- The window functional `t` of the fraction `(n, d)` on a vector `(v₁, v₂)`. -/
def tq (n d : ℚ) (v : ℚ × ℚ) : ℚ := n * v.1 - d * v.2

/-- The window functional `s` of the fraction `(n, d)` on a vector `(v₁, v₂)`. -/
def sq (n d : ℚ) (v : ℚ × ℚ) : ℚ := (d + n) * v.1 + (d - n) * v.2

/-- The `T` of the fraction `(n, d)`: `d² + 2dn − n²`. -/
def Tq (n d : ℚ) : ℚ := d ^ 2 + 2 * d * n - n ^ 2

/-- The child vector `X = mP + Q` in `(d, n)` coordinates (`P = (dP, nP)`, `Q = (dQ, nQ)`). -/
def Xv (m dP nP dQ nQ : ℚ) : ℚ × ℚ := (m * dP + dQ, m * nP + nQ)

/-- The period operation `V(d, n) = (n − d, d + n)` on `(d, n)` vectors. -/
def Vv (v : ℚ × ℚ) : ℚ × ℚ := (v.2 - v.1, v.1 + v.2)

/-- `t_P(X) = −δ` for the child `X = mP + Q`, with `δ = dP nQ − nP dQ`. -/
theorem tq_Xv (m dP nP dQ nQ : ℚ) :
    tq nP dP (Xv m dP nP dQ nQ) = -(dP * nQ - nP * dQ) := by
  simp only [tq, Xv]
  ring

/-- `t_P(V_P) = −T_P`. -/
theorem tq_VP (dP nP : ℚ) : tq nP dP (Vv (dP, nP)) = -Tq nP dP := by
  simp only [tq, Vv, Tq]
  ring

/-- `t_P(V_Q) = −s_P(Q)`. -/
theorem tq_VQ (dP nP dQ nQ : ℚ) :
    tq nP dP (Vv (dQ, nQ)) = -sq nP dP (dQ, nQ) := by
  simp only [tq, Vv, sq]
  ring

/-- **The `t` of the period `V_X`:** `t_P(V_X) = −(m T_P + s_P(Q))`, since `V` is linear. -/
theorem tq_VX (m dP nP dQ nQ : ℚ) :
    tq nP dP (Vv (Xv m dP nP dQ nQ)) = -(m * Tq nP dP + sq nP dP (dQ, nQ)) := by
  simp only [tq, Vv, Xv, Tq, sq]
  ring

/-- **The `s` of the period `V_X`:** `s_P(V_X)` in terms of `δ` (the note's `s_X(V_P) = −2δ`, `s_X(V_Q) = 4δ` at `m = 1`). -/
theorem sq_VX (m dP nP dQ nQ : ℚ) :
    sq nP dP (Vv (Xv m dP nP dQ nQ)) = m * sq nP dP (Vv (dP, nP)) + sq nP dP (Vv (dQ, nQ)) := by
  simp only [sq, Vv, Xv]
  ring

end FLatticePaper.Tiles.PairCellForms
