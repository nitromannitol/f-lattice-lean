import FLatticePaper.Tiles.PairBoxesP0

/-! Task 53, item 2 (covering reduction), section 5b: the box of the odd parent `P` at zero offset, at EVEN sites.

Same box `0 ≤ u, v ≤ α` with `α = d/(d + e)`, and the same parent functionals as `PairBoxesP0`:
`t = (d + n)/2 + 2u − (T + K) v`, `s = n + 2(T + K) u − 2v`, `T = d² + 2dn − n²`, `K = (d + n) e + (d − n) r`.
At even sites (`ev = true`, `μ = 2` since `d + n` is odd) the window of `P` has `a = min(2n, d − n)` and `l = 0`:
`a − T ≤ t ≤ d + n − a` and `0 ≤ s ≤ 2T + 2n`. The four lemmas are these real bounds with the integer mesh slack `1`.

The upper `t` bound reduces to `4d < (d + n − 2m + 2)(d + e)`, `m = min(2n, d − n)`. This can fail only for `(e, r) = (3, 1)`
(then `d = 3n − 1`, and the bound fails once `n ≥ 4`); that is the note's exceptional family, which needs another source cell.
`t_upper_even` therefore assumes `¬ (e = 3 ∧ r = 1)`. -/

namespace FLatticePaper.Tiles.PairBoxesP0Even

/-- The integer corner inequality `4d < (d + n − 2m + 2)(d + e)` for `m = min(2n, d − n)`, outside `(e, r) = (3, 1)`. -/
theorem corner_even (d n e r m : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (hnot : ¬ (e = 3 ∧ r = 1))
    (hm : m = min (2 * n) (d - n)) :
    4 * d < (d + n - 2 * m + 2) * (d + e) := by
  have he : 0 < d + e := by omega
  have hne : d - 3 * n ≠ 0 := by omega
  rcases le_or_gt d (3 * n) with hA | hB
  · have hmA : m = d - n := by omega
    rw [hmA]
    rcases (show 3 * n - d = 1 ∨ 2 ≤ 3 * n - d by omega) with h1 | h2
    · -- `d = 3n − 1`: the bound needs `e ≥ n`, which holds outside `(e, r) = (3, 1)`
      have hd' : d = 3 * n - 1 := by omega
      have hq : n * (3 * r - e) = r - 1 := by linear_combination hdet - r * hd'
      have hen : n ≤ e := by
        by_contra hc
        have hlt : e ≤ n - 1 := by omega
        rcases le_or_gt (3 * r - e) 0 with hq0 | hq1
        · have hle : n * (3 * r - e) ≤ n * 0 := mul_le_mul_of_nonneg_left hq0 hn.le
          have hr1' : r ≤ 1 := by linarith
          have hr1 : r = 1 := by omega
          have h0 : n * (3 * r - e) = 0 := by
            rw [hq]
            omega
          rcases mul_eq_zero.mp h0 with h | h
          · omega
          · exact hnot ⟨by omega, hr1⟩
        · have hle : n * 1 ≤ n * (3 * r - e) := mul_le_mul_of_nonneg_left (by omega) hn.le
          have hrn : r - 1 < n := by omega
          linarith
      have h3 : d + n - 2 * (d - n) + 2 = 3 := by omega
      rw [h3]
      omega
    · have h4 : 4 * (d + e) ≤ (d + n - 2 * (d - n) + 2) * (d + e) :=
        mul_le_mul_of_nonneg_right (by omega) he.le
      linarith
  · have hmB : m = 2 * n := by omega
    rw [hmB]
    rcases (show d - 3 * n = 1 ∨ 2 ≤ d - 3 * n by omega) with h1 | h2
    · -- `d = 3n + 1`: the bound needs `e ≥ n + 1`
      have hd' : d = 3 * n + 1 := by omega
      have hq : n * (3 * r - e) = -(r + 1) := by linear_combination hdet - r * hd'
      have hen : n + 1 ≤ e := by
        by_contra hc
        have hle' : e ≤ n := by omega
        rcases le_or_gt 0 (3 * r - e) with hq0 | hq1
        · have hnn := mul_nonneg hn.le hq0
          linarith
        · have hle : n * (3 * r - e) ≤ n * (-1) := mul_le_mul_of_nonneg_left (by omega) hn.le
          have hnr : n ≤ r + 1 := by linarith
          omega
      have h3 : d + n - 2 * (2 * n) + 2 = 3 := by omega
      rw [h3]
      omega
    · have h4 : 4 * (d + e) ≤ (d + n - 2 * (2 * n) + 2) * (d + e) :=
        mul_le_mul_of_nonneg_right (by omega) he.le
      linarith

/-- The real `t` of the box at even sites: upper bound `t < d + n − m + 1` with `m = min(2n, d − n)` (mesh slack `1`). -/
theorem t_upper_even (d n e r m : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (hnot : ¬ (e = 3 ∧ r = 1))
    (hm : m = min (2 * n) (d - n))
    (u v : ℚ) (_hu0 : 0 ≤ u) (hu1 : u ≤ (d : ℚ) / (d + e)) (hv0 : 0 ≤ v) :
    ((d : ℚ) + n) / 2 + 2 * u - (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * v
      < (d : ℚ) + n - (m : ℚ) + 1 := by
  have hc := corner_even d n e r m hn hnd hr hre hdet hodd hnot hm
  have hD : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have hcQ : (4 : ℚ) * d < ((d : ℚ) + n - 2 * m + 2) * ((d : ℚ) + e) := by exact_mod_cast hc
  have h4 : 4 * ((d : ℚ) / (d + e)) < (d : ℚ) + n - 2 * m + 2 := by
    rw [show (4 : ℚ) * ((d : ℚ) / (d + e)) = 4 * d / (d + e) by ring, div_lt_iff₀ hD]
    linarith
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  have hnd' : (n : ℚ) < d := by exact_mod_cast hnd
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have he' : (0 : ℚ) < e := by
    have : (0 : ℤ) < e := by omega
    exact_mod_cast this
  have hd' : (0 : ℚ) < d := by linarith
  have hTK : (0 : ℚ) ≤ ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ) := by
    nlinarith
  have hTv : 0 ≤ (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * v :=
    mul_nonneg hTK hv0
  have h2u : 2 * u ≤ 2 * ((d : ℚ) / (d + e)) := by linarith
  linarith

/-- The real `t` of the box at even sites: lower bound `t > m − T − 1` with `m = min(2n, d − n)` (mesh slack `1`). -/
theorem t_lower_even (d n e r m : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hm : m = min (2 * n) (d - n))
    (u v : ℚ) (hu0 : 0 ≤ u) (hv1 : v ≤ (d : ℚ) / (d + e)) :
    (m : ℚ) - ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) - 1 <
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
  have hcpos : (0 : ℚ) < ((d : ℚ) - n) / ((d : ℚ) + e) := by
    apply div_pos <;> linarith
  have hv : (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * v
      ≤ ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) - ((d : ℚ) - n) / ((d : ℚ) + e) := by
    have := mul_le_mul_of_nonneg_left hv1 hTK
    linarith
  have hm2 : 2 * (m - 1) ≤ d + n := by omega
  have hm2' : 2 * ((m : ℚ) - 1) ≤ (d : ℚ) + n := by exact_mod_cast hm2
  linarith

/-- The real `s` of the box at even sites: lower bound `s > −1` (window `s ≥ 0`, with mesh slack). -/
theorem s_lower_even (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (u v : ℚ) (hu0 : 0 ≤ u) (hv1 : v ≤ (d : ℚ) / (d + e)) :
    (0 : ℚ) - 1 < (n : ℚ) + 2 * (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * u - 2 * v := by
  have hn' : (1 : ℚ) ≤ n := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
  have hnd' : (n : ℚ) < d := by exact_mod_cast hnd
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have he' : (0 : ℚ) < e := by
    have : (0 : ℤ) < e := by omega
    exact_mod_cast this
  have hD : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have hTK : (0 : ℚ) ≤ ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ) := by
    nlinarith
  have hα1 : (d : ℚ) / (d + e) < 1 := by
    rw [div_lt_one hD]
    linarith
  have hTu : 0 ≤ (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * u :=
    mul_nonneg hTK hu0
  linarith

/-- The real `s` of the box at even sites: upper bound `s < 2T + 2n + 1` (window `s ≤ 2T + 2n`, with mesh slack). -/
theorem s_upper_even (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1)
    (u v : ℚ) (hu1 : u ≤ (d : ℚ) / (d + e)) (hv0 : 0 ≤ v) :
    (n : ℚ) + 2 * (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * u - 2 * v <
      2 * ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + 2 * n + 1 := by
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
  have hcpos : (0 : ℚ) < ((d : ℚ) - n) / ((d : ℚ) + e) := by
    apply div_pos <;> linarith
  have hTu : (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * u
      ≤ (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * ((d : ℚ) / (d + e)) :=
    mul_le_mul_of_nonneg_left hu1 hTK
  linarith

end FLatticePaper.Tiles.PairBoxesP0Even
