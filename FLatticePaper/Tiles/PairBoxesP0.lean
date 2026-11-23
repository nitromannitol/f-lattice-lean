import FLatticePaper.Tiles.PairMargins
import FLatticePaper.Tiles.PairCellWindows

/-! Task 53, item 2 (covering reduction), section 5: the box of the odd parent `P` at zero offset, for `δ = dr − ne = −1`
(the flag-true odd child of `SitePairScope`, the note's W1).

On the box `0 ≤ u, v ≤ α`, `α = d/(d + e)`, the cell point `B0 + uU + vV` has the parent-`P` functionals
`t = (d + n)/2 + 2u − (T + K) v` and `s = n + 2(T + K) u − 2 v` (`T = T_P`, `K = s_P(Q)`).
The identity `d(T + K) = (d + e) T − c` (`c = d − n`, from `dK − eT = cδ`) gives the corners of the window.
At odd sites (`a = n`, `l = min(c, 3n − d)`) the four window inequalities hold with the integer mesh slack `1`:
`n − T − 1 < t < d + 1` and `l − 1 < s < 2T + 2n − l + 1`. -/

namespace FLatticePaper.Tiles.PairBoxesP0

/-- The real `t` of the box at odd sites: upper bound `t < d + 1` (the window `t ≤ L − n = d`, with mesh slack). -/
theorem t_upper_odd (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (heven : (e + r) % 2 = 0) (hodd : (d + n) % 2 = 1) (hdet : d * r - n * e = -1)
    (u v : ℚ) (_hu0 : 0 ≤ u) (hu1 : u ≤ (d : ℚ) / (d + e)) (hv0 : 0 ≤ v) (_hv1 : v ≤ (d : ℚ) / (d + e)) :
    ((d : ℚ) + n) / 2 + 2 * u - (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * v < d + 1 := by
  have hm := FLatticePaper.Tiles.PairMargins.margin_t_odd_m1 d n e r hn hnd hodd hr hre heven (Or.inr hdet)
  have hmQ : (2 : ℚ) * (2 * d + (d - n)) < ((d - n) + 2) * (d + e) := by exact_mod_cast hm
  have hD : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have hTK : (0 : ℚ) ≤ ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ) := by
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    have hnd' : (n : ℚ) < d := by exact_mod_cast hnd
    have hr' : (0 : ℚ) < r := by exact_mod_cast hr
    have he' : (0 : ℚ) < e := by
      have : (0 : ℤ) < e := by omega
      exact_mod_cast this
    have hd' : (0 : ℚ) < d := by linarith
    nlinarith
  have h2u : 2 * u ≤ 2 * ((d : ℚ) / (d + e)) := by linarith
  have h4 : 4 * ((d : ℚ) / (d + e)) < (d : ℚ) - n + 2 := by
    have h4' : (4 : ℚ) * ((d : ℚ) / (d + e)) = 4 * d / (d + e) := by ring
    have hnd' : (n : ℚ) < d := by exact_mod_cast hnd
    rw [h4', div_lt_iff₀ hD]
    nlinarith [hmQ, hnd']
  have hTv : 0 ≤ ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2 + ((d + n) * e + (d - n) * r : ℚ)) * v :=
    mul_nonneg hTK hv0
  linarith

/-- The real `t` of the box at odd sites: lower bound `t > n − T − 1` (window `t ≥ a − T = n − T`, with mesh slack). -/
theorem t_lower_odd (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1)
    (u v : ℚ) (hu0 : 0 ≤ u) (_hv0 : 0 ≤ v) (hv1 : v ≤ (d : ℚ) / (d + e)) :
    (n : ℚ) - ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) - 1 <
      ((d : ℚ) + n) / 2 + 2 * u - (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * v := by
  have hD : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have hdetQ : (d : ℚ) * r - n * e = -1 := by exact_mod_cast hdet
  have hnd' : (n : ℚ) < d := by exact_mod_cast hnd
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have he' : (0 : ℚ) < e := by
    have : (0 : ℤ) < e := by omega
    exact_mod_cast this
  have hTK : (0 : ℚ) ≤ ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ) := by
    nlinarith
  -- d (T + K) = (d + e) T − c, from d K − e T = c δ with δ = −1
  have hT'd : (d : ℚ) * ((((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ))) =
      ((d : ℚ) + e) * ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) - ((d : ℚ) - n) := by
    linear_combination ((d : ℚ) - n) * hdetQ
  have hcorner : (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * ((d : ℚ) / (d + e))
      = ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) - ((d : ℚ) - n) / ((d : ℚ) + e) := by
    field_simp
    linear_combination hT'd
  have hcn : (0 : ℚ) ≤ ((d : ℚ) - n) / ((d : ℚ) + e) := by
    apply div_nonneg <;> linarith
  have hv : (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * v
      ≤ ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) := by
    have := mul_le_mul_of_nonneg_left hv1 hTK
    linarith
  linarith

/-- The real `s` of the box at odd sites: lower bound `s > l − 1` (window `s ≥ l`, with mesh slack), for `l = min(c, 3n − d)`. -/
theorem s_lower_odd (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1)
    (u v : ℚ) (hu0 : 0 ≤ u) (_hv0 : 0 ≤ v) (hv1 : v ≤ (d : ℚ) / (d + e)) (heven : (e + r) % 2 = 0) :
    ((min (d - n) (3 * n - d) : ℤ) : ℚ) - 1 <
      (n : ℚ) + 2 * (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * u - 2 * v := by
  have hd2 : 2 ≤ d := by omega
  have hTK : (0 : ℚ) ≤ ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ) := by
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    have hnd' : (n : ℚ) < d := by exact_mod_cast hnd
    have hr' : (0 : ℚ) < r := by exact_mod_cast hr
    have he' : (0 : ℚ) < e := by
      have : (0 : ℤ) < e := by omega
      exact_mod_cast this
    nlinarith
  have hD : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have hα : 2 * ((d : ℚ) / (d + e)) < 2 := by
    have he' : (0 : ℚ) < e := by
      have : (0 : ℤ) < e := by omega
      exact_mod_cast this
    have : (d : ℚ) / (d + e) < 1 := by
      rw [div_lt_one hD]
      linarith
    linarith
  have hTu : 0 ≤ (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * u :=
    mul_nonneg hTK hu0
  rcases (show n - min (d - n) (3 * n - d) ≥ 1 ∨ 2 * n = d by omega) with hA | hB
  · have hA2 : (1 : ℚ) ≤ (n : ℚ) - ((min (d - n) (3 * n - d) : ℤ) : ℚ) := by
      have h : (1 : ℤ) ≤ n - min (d - n) (3 * n - d) := hA
      have h' : (1 : ℚ) ≤ ((n - min (d - n) (3 * n - d) : ℤ) : ℚ) := by exact_mod_cast h
      rw [Int.cast_sub] at h'
      linarith
    linarith
  · have hn1 : n = 1 := by
      have hk : n * (2 * r - e) = -1 := by
        have h2 : (2 * n) * r - n * e = -1 := by rw [hB]; exact hdet
        linarith [show (2 * n) * r - n * e = n * (2 * r - e) by ring]
      exact FLatticePaper.Tiles.PairMargins.pm_one_unit n (2 * r - e) hn (Or.inr hk)
    have hd2' : d = 2 := by omega
    have hcn : (n : ℚ) = 1 := by exact_mod_cast hn1
    have hcd : (d : ℚ) = 2 := by exact_mod_cast hd2'
    have hl1 : ((min (d - n) (3 * n - d) : ℤ) : ℚ) = 1 := by
      have : min (d - n) (3 * n - d) = 1 := by omega
      exact_mod_cast this
    have hv' : v ≤ 2 / (2 + e) := by
      rw [← hcd]
      simpa using hv1
    have he3 : (3 : ℚ) ≤ e := by
      have : (3 : ℤ) ≤ e := by omega
      exact_mod_cast this
    have hq : (2 : ℚ) / (2 + e) < 1 / 2 := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    rw [hl1]
    linarith

/-- The real `s` of the box at odd sites: upper bound `s < 2T + 2n − l + 1` (window `s ≤ 2T + 2n − l`, with mesh slack). -/
theorem s_upper_odd (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1)
    (u v : ℚ) (_hu0 : 0 ≤ u) (hu1 : u ≤ (d : ℚ) / (d + e)) (hv0 : 0 ≤ v) :
    (n : ℚ) + 2 * (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * u - 2 * v <
      2 * ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + 2 * n - ((min (d - n) (3 * n - d) : ℤ) : ℚ) + 1 := by
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hnd' : (n : ℚ) < d := by exact_mod_cast hnd
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have hD : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have he' : (0 : ℚ) < e := by
    have : (0 : ℤ) < e := by omega
    exact_mod_cast this
  have hTK : (0 : ℚ) ≤ ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ) := by
    nlinarith
  have hdetQ : (d : ℚ) * r - n * e = -1 := by exact_mod_cast hdet
  have hT'd : (d : ℚ) * ((((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ))) =
      ((d : ℚ) + e) * ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) - ((d : ℚ) - n) := by
    linear_combination ((d : ℚ) - n) * hdetQ
  have hcorner : (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * ((d : ℚ) / (d + e))
      = ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) - ((d : ℚ) - n) / ((d : ℚ) + e) := by
    field_simp
    linear_combination hT'd
  have hcn : (0 : ℚ) ≤ ((d : ℚ) - n) / ((d : ℚ) + e) := by
    apply div_nonneg <;> linarith
  have hTu : (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * u
      ≤ (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * ((d : ℚ) / (d + e)) :=
    mul_le_mul_of_nonneg_left hu1 hTK
  have hl0 : (0 : ℚ) ≤ (n : ℚ) - ((min (d - n) (3 * n - d) : ℤ) : ℚ) := by
    have h : (0 : ℤ) ≤ n - min (d - n) (3 * n - d) := by omega
    have h' : (0 : ℚ) ≤ ((n - min (d - n) (3 * n - d) : ℤ) : ℚ) := by exact_mod_cast h
    rw [Int.cast_sub] at h'
    linarith
  have hv0' : (0 : ℚ) ≤ v := hv0
  linarith

end FLatticePaper.Tiles.PairBoxesP0
