import FLatticePaper.Plane.Induction.FreeRows

/-! # The levels of the V cut (task 110, step (2)): Q13's `D_±` values and their rounded `J_± = ⌈D_±/2⌉`

Q13's insertion gives, on the V cut `V_0, …, V_{L−1}` (`r = D+N`, `L = d+n`):
* minus: `D_-(V_0) = 0`, `D_-(V_j) = −1` for `1 ≤ j ≤ r`, `D_-(V_j) = −2` for `r < j < L`;
* plus raw: `0` for `j ≤ L − r − 2`, `1` for the next `r` vertices, `2` at the final vertex `V_{L−1}`.

The rounded levels are `J = ⌈D/2⌉ = (D + 1)/2`. The lemmas below prove that `J_-` changes after `r` and `J_+` after `L − r − 2`, as Q13 states.

The label levels: for a V label `V_j` with `0 ≤ j < L` the level is the value on the cut. The labels `V_j` with `j < 0` (and `j ≥ L`) are deck translates
of cut labels, and their level shift (the translation coefficient `−ηJ_η`) is a named input here, not yet stated. The window per level (the parabola
lies below `F`) is also named (`FreeRows.free_row_empty`). -/

namespace FLatticePaper.FreeLevels

/-- The minus raw slip on the V cut: `0` at `V_0`, `−1` for `1 ≤ j ≤ r`, `−2` for `r < j`. -/
def dMinusV (r j : ℤ) : ℤ := if j = 0 then 0 else if j ≤ r then -1 else -2

/-- The plus raw slip on the V cut: `0` for `j ≤ L − r − 2`, `1` for the next vertices, `2` at the final vertex `V_{L−1}`. -/
def dPlusV (r L j : ℤ) : ℤ := if j ≤ L - r - 2 then 0 else if j < L - 1 then 1 else 2

/-- The rounded level `J = ⌈D/2⌉ = (D+1)/2`. -/
def jOf (D : ℤ) : ℤ := (D + 1) / 2

/-- **The minus rounded level changes after `r`**: `J_-(V_j) = 0` for `0 ≤ j ≤ r`, and `−1` for `r < j < L`. -/
theorem jMinusV_level (r j : ℤ) (hr : 0 ≤ r) :
    jOf (dMinusV r j) = if j ≤ r then 0 else -1 := by
  unfold jOf dMinusV
  split_ifs <;> omega

/-- **The plus rounded level changes after `L − r − 2`**: `J_+(V_j) = 0` for `j ≤ L − r − 2`, and `1` for `L − r − 2 < j < L`. -/
theorem jPlusV_level (r L j : ℤ) :
    jOf (dPlusV r L j) = if j ≤ L - r - 2 then 0 else 1 := by
  unfold jOf dPlusV
  split_ifs <;> omega

/-- The minus level is nonincreasing along the cut: `J_-` drops once, after `r` (Q13's “minus level changes after r”). -/
theorem jMinusV_drop (r j : ℤ) (hr : 0 ≤ r) :
    jOf (dMinusV r j) = 0 ∨ jOf (dMinusV r j) = -1 := by
  rw [jMinusV_level r j hr]
  split_ifs <;> simp

end FLatticePaper.FreeLevels
