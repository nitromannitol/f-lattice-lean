import FLatticePaper.Tiles.PairMargins
import FLatticePaper.Tiles.PairCellWindows

/-! Task 53, item 2 (covering reduction), section 4: the lower t bound on the box of `P` at zero offset, for the sign
`δ = dr − ne = +1` (the note's W0 pairing; the flag-true odd child, with P at zero offset, is `δ = −1`, see `PairBoxesP0`).
The first box facet.

The source `P` at offset `0` (the flag-true odd child) covers the cell points `B0 + uU + vV` with `0 ≤ u, v ≤ α`, `α = d/(d + e)`
(`d = d_P`, `e = d_Q`, `δ = dr − ne = 1`). Its lower `t` window at an odd site is `t ≥ n − T`. The real `t` on the box is
`(d + n)/2 − 2u − (T + K) v` (`T = T_P`, `K = s_P(Q)`), and the minimum over the box is attained at `u = v = α`. The identity
`d(2 + T + K) = (d + e)T + 2d + (d − n)` (from `dK − eT = (d − n)δ`) turns that corner into the margin `margin_t_odd_m1`. -/

namespace FLatticePaper.Tiles.PairBoxes

/-- The corner of the lower `t` facet of `P` at odd sites, with the integer mesh slack `1`: strict. -/
theorem box_P0_t_lower_odd (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (heven : (e + r) % 2 = 0) (hodd : (d + n) % 2 = 1) (hdet : d * r - n * e = 1)
    (u v : ℚ) (_hu0 : 0 ≤ u) (hu1 : u ≤ (d : ℚ) / (d + e)) (_hv0 : 0 ≤ v) (hv1 : v ≤ (d : ℚ) / (d + e)) :
    (n : ℚ) - ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) - 1 <
      ((d : ℚ) + n) / 2 - 2 * u - (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * v := by
  have hm := FLatticePaper.Tiles.PairMargins.margin_t_odd_m1 d n e r hn hnd hodd hr hre heven (Or.inl hdet)
  have hmQ : (2 : ℚ) * (2 * d + (d - n)) < ((d - n) + 2) * (d + e) := by exact_mod_cast hm
  have hD : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have hdetQ : (d : ℚ) * r - n * e = 1 := by exact_mod_cast hdet
  set T : ℚ := (d : ℚ) ^ 2 + 2 * d * n - n ^ 2 with hT
  set K : ℚ := (d + n) * e + (d - n) * r with hK
  have hTK : 0 ≤ T + K := by
    have hdn : (0 : ℚ) ≤ d - n := by
      have : (n : ℤ) < d := hnd
      have hq : (n : ℚ) < d := by exact_mod_cast this
      linarith
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    have hd' : (0 : ℚ) < d := by linarith
    have he' : (0 : ℚ) < e := by
      have : (0 : ℤ) < e := by omega
      exact_mod_cast this
    have hr' : (0 : ℚ) < r := by exact_mod_cast hr
    have hT0 : 0 ≤ T := by rw [hT]; nlinarith
    have hK0 : 0 ≤ K := by rw [hK]; nlinarith
    linarith
  -- the identity d (2 + T + K) = (d + e) T + 2d + (d − n), from dK − eT = (d − n)(dr − ne) = d − n
  have hkey : (d : ℚ) * (2 + T + K) = ((d : ℚ) + e) * T + 2 * d + ((d : ℚ) - n) := by
    rw [hT, hK]
    linear_combination ((d : ℚ) - n) * hdetQ
  -- the upper bound of `2u + (T + K) v` on the box
  have hbound : 2 * u + (T + K) * v ≤ (2 + T + K) * ((d : ℚ) / (d + e)) := by
    have h1 : 2 * u ≤ 2 * ((d : ℚ) / (d + e)) := by linarith
    have h2 : (T + K) * v ≤ (T + K) * ((d : ℚ) / (d + e)) := by
      exact mul_le_mul_of_nonneg_left hv1 hTK
    nlinarith
  -- the corner value is above the bound
  have hdiv : (2 * (d : ℚ) + (d - n)) / (d + e) < ((d : ℚ) - n) / 2 + 1 := by
    rw [div_lt_iff₀ hD]
    nlinarith [hmQ]
  have e1 : (2 + T + K) * ((d : ℚ) / (d + e)) = T + (2 * d + ((d : ℚ) - n)) / (d + e) := by
    field_simp
    linear_combination hkey
  have hcorner : (2 + T + K) * ((d : ℚ) / (d + e)) < ((d : ℚ) + n) / 2 - n + T + 1 := by
    rw [e1]
    linarith [hdiv]
  linarith

end FLatticePaper.Tiles.PairBoxes
