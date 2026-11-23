import FLatticePaper.Tiles.PairMargins

/-! Task 53, item 2 (covering reduction), section 1: the nominal parents.

For proper parents `P = (dP, nP)` (odd) and `Q = (dQ, nQ)` (even), with `X = mP + Q` (`m = 1` odd child, `m = 2` even child),
`D = m dP + dQ` and `δ = dP nQ − nP dQ` (the determinant `dr − ne` of the note), the nominal parents `P̄ = (dP/D) X` and
`Q̄ = (dQ/D) X` differ from the actual parents by `P − P̄ = (0, −δ/D)` and `Q − Q̄ = (0, mδ/D)`. The period operation
`V(d,n) = (n − d, d + n)` maps these differences to multiples of `(1,1)`: `V(0,c) = (c, c)`. -/

namespace FLatticePaper.Tiles.PairNominal

/-- The first coordinate of the nominal odd parent is exact: `dP − (dP/D)·D = 0`. -/
theorem nominal_P_fst (m dP dQ : ℚ) (hD : m * dP + dQ ≠ 0) :
    dP - dP / (m * dP + dQ) * (m * dP + dQ) = 0 := by
  rw [div_mul_cancel₀ dP hD]
  ring

/-- The second coordinate of `P − P̄` is `−δ/D`. -/
theorem nominal_P_snd (m dP nP dQ nQ : ℚ) (hD : m * dP + dQ ≠ 0) :
    nP - dP / (m * dP + dQ) * (m * nP + nQ) = -(dP * nQ - nP * dQ) / (m * dP + dQ) := by
  have hinv : (m * dP + dQ) * (m * dP + dQ)⁻¹ = 1 := mul_inv_cancel₀ hD
  simp only [div_eq_mul_inv]
  linear_combination (-nP) * hinv

/-- The first coordinate of `Q − Q̄` is exact: `dQ − (dQ/D)·D = 0`. -/
theorem nominal_Q_fst (m dP dQ : ℚ) (hD : m * dP + dQ ≠ 0) :
    dQ - dQ / (m * dP + dQ) * (m * dP + dQ) = 0 := by
  rw [div_mul_cancel₀ dQ hD]
  ring

/-- The second coordinate of `Q − Q̄` is `mδ/D`. -/
theorem nominal_Q_snd (m dP nP dQ nQ : ℚ) (hD : m * dP + dQ ≠ 0) :
    nQ - dQ / (m * dP + dQ) * (m * nP + nQ) = m * (dP * nQ - nP * dQ) / (m * dP + dQ) := by
  have hinv : (m * dP + dQ) * (m * dP + dQ)⁻¹ = 1 := mul_inv_cancel₀ hD
  simp only [div_eq_mul_inv]
  linear_combination (-nQ) * hinv

/-- The period operation `V(d, n) = (n − d, d + n)`. -/
def Vop (v : ℚ × ℚ) : ℚ × ℚ := (v.2 - v.1, v.1 + v.2)

/-- `V` of a vertical displacement `(0, c)` is `c (1, 1)`. -/
theorem Vop_vertical (c : ℚ) : Vop (0, c) = (c, c) := by
  simp [Vop]

end FLatticePaper.Tiles.PairNominal
