import FLatticePaper.Plane.Induction.AlignedClassGrade

/-! # A bottom witness and a top-type neighbour cannot both occur (step (4), bottom case)

For a grade point `(t, s)` with a bottom witness (a neighbour `t_b` with `FHr`, so `1 ≤ t_b`) and a top-type witness (a neighbour `t_w`
with `FHr` at `t_w + T`, so `t_w + T ≤ d + n`), the two neighbours are at grade distance at most `2(d + n)` (both are within one pixel of
`(t, s)`). Since `t_b - t_w ≥ T - d - n + 1` and `T ≥ 3(d + n)`, this is a contradiction (`bot_key`). Only the grades of the two
neighbours are used; no strictness of the centre. -/

namespace FLatticePaper.BottomTopEmpty

open FLatticePaper.AlignedClassGrade

/-- The period bound `3(d + n) ≤ T`, from `T = d² + 2dn - n²`, `n ≥ 1`, `d ≥ n + 2`. -/
theorem period_ge (n d T : Int) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d) (hTdef : T = d * d + 2 * d * n - n * n) :
    3 * (d + n) ≤ T := by
  have he : (0 : Int) ≤ d - n - 2 := by omega
  rw [hTdef]
  nlinarith [mul_nonneg he (show (0 : Int) ≤ n by omega), mul_nonneg he he]

/-- The key contradiction on grades. -/
theorem bot_key (n d T tb tw : Int) (hT3 : 3 * (d + n) ≤ T)
    (hb : 1 ≤ tb) (hw : tw + T ≤ d + n) (hdist : tb - tw ≤ 2 * n + 2 * d) : False := by
  omega

theorem bot_top_mm (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n)
    (hnd : n + 2 ≤ d) (hT3 : 3 * (d + n) ≤ T)
    (hB : FHr n d T (t + n * (-1) - d * (-1)) (s + (d + n) * (-1) + (d - n) * (-1)))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) : False := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FHr, ClG, hSpG] at hB hT2
  · exact bot_key n d T (t + n * (-1) - d * (-1)) (t + n * (-1) - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * (-1)) (t + n * (-1) - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * (-1)) (t + n * (-1) - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * (-1)) (t + n * 0 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * (-1)) (t + n * 0 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * (-1)) (t + n * 0 - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * (-1)) (t + n * 1 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * (-1)) (t + n * 1 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * (-1)) (t + n * 1 - d * 1) hT3 (by omega) (by omega) (by omega)
theorem bot_top_mz (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n)
    (hnd : n + 2 ≤ d) (hT3 : 3 * (d + n) ≤ T)
    (hB : FHr n d T (t + n * (-1) - d * 0) (s + (d + n) * (-1) + (d - n) * 0))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) : False := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FHr, ClG, hSpG] at hB hT2
  · exact bot_key n d T (t + n * (-1) - d * 0) (t + n * (-1) - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 0) (t + n * (-1) - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 0) (t + n * (-1) - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 0) (t + n * 0 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 0) (t + n * 0 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 0) (t + n * 0 - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 0) (t + n * 1 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 0) (t + n * 1 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 0) (t + n * 1 - d * 1) hT3 (by omega) (by omega) (by omega)
theorem bot_top_mp (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n)
    (hnd : n + 2 ≤ d) (hT3 : 3 * (d + n) ≤ T)
    (hB : FHr n d T (t + n * (-1) - d * 1) (s + (d + n) * (-1) + (d - n) * 1))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) : False := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FHr, ClG, hSpG] at hB hT2
  · exact bot_key n d T (t + n * (-1) - d * 1) (t + n * (-1) - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 1) (t + n * (-1) - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 1) (t + n * (-1) - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 1) (t + n * 0 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 1) (t + n * 0 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 1) (t + n * 0 - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 1) (t + n * 1 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 1) (t + n * 1 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * (-1) - d * 1) (t + n * 1 - d * 1) hT3 (by omega) (by omega) (by omega)
theorem bot_top_zm (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n)
    (hnd : n + 2 ≤ d) (hT3 : 3 * (d + n) ≤ T)
    (hB : FHr n d T (t + n * 0 - d * (-1)) (s + (d + n) * 0 + (d - n) * (-1)))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) : False := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FHr, ClG, hSpG] at hB hT2
  · exact bot_key n d T (t + n * 0 - d * (-1)) (t + n * (-1) - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * (-1)) (t + n * (-1) - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * (-1)) (t + n * (-1) - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * (-1)) (t + n * 0 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * (-1)) (t + n * 0 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * (-1)) (t + n * 0 - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * (-1)) (t + n * 1 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * (-1)) (t + n * 1 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * (-1)) (t + n * 1 - d * 1) hT3 (by omega) (by omega) (by omega)
theorem bot_top_zz (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n)
    (hnd : n + 2 ≤ d) (hT3 : 3 * (d + n) ≤ T)
    (hB : FHr n d T (t + n * 0 - d * 0) (s + (d + n) * 0 + (d - n) * 0))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) : False := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FHr, ClG, hSpG] at hB hT2
  · exact bot_key n d T (t + n * 0 - d * 0) (t + n * (-1) - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 0) (t + n * (-1) - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 0) (t + n * (-1) - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 0) (t + n * 0 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 0) (t + n * 0 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 0) (t + n * 0 - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 0) (t + n * 1 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 0) (t + n * 1 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 0) (t + n * 1 - d * 1) hT3 (by omega) (by omega) (by omega)
theorem bot_top_zp (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n)
    (hnd : n + 2 ≤ d) (hT3 : 3 * (d + n) ≤ T)
    (hB : FHr n d T (t + n * 0 - d * 1) (s + (d + n) * 0 + (d - n) * 1))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) : False := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FHr, ClG, hSpG] at hB hT2
  · exact bot_key n d T (t + n * 0 - d * 1) (t + n * (-1) - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 1) (t + n * (-1) - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 1) (t + n * (-1) - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 1) (t + n * 0 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 1) (t + n * 0 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 1) (t + n * 0 - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 1) (t + n * 1 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 1) (t + n * 1 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 0 - d * 1) (t + n * 1 - d * 1) hT3 (by omega) (by omega) (by omega)
theorem bot_top_pm (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n)
    (hnd : n + 2 ≤ d) (hT3 : 3 * (d + n) ≤ T)
    (hB : FHr n d T (t + n * 1 - d * (-1)) (s + (d + n) * 1 + (d - n) * (-1)))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) : False := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FHr, ClG, hSpG] at hB hT2
  · exact bot_key n d T (t + n * 1 - d * (-1)) (t + n * (-1) - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * (-1)) (t + n * (-1) - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * (-1)) (t + n * (-1) - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * (-1)) (t + n * 0 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * (-1)) (t + n * 0 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * (-1)) (t + n * 0 - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * (-1)) (t + n * 1 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * (-1)) (t + n * 1 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * (-1)) (t + n * 1 - d * 1) hT3 (by omega) (by omega) (by omega)
theorem bot_top_pz (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n)
    (hnd : n + 2 ≤ d) (hT3 : 3 * (d + n) ≤ T)
    (hB : FHr n d T (t + n * 1 - d * 0) (s + (d + n) * 1 + (d - n) * 0))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) : False := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FHr, ClG, hSpG] at hB hT2
  · exact bot_key n d T (t + n * 1 - d * 0) (t + n * (-1) - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 0) (t + n * (-1) - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 0) (t + n * (-1) - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 0) (t + n * 0 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 0) (t + n * 0 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 0) (t + n * 0 - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 0) (t + n * 1 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 0) (t + n * 1 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 0) (t + n * 1 - d * 1) hT3 (by omega) (by omega) (by omega)
theorem bot_top_pp (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n)
    (hnd : n + 2 ≤ d) (hT3 : 3 * (d + n) ≤ T)
    (hB : FHr n d T (t + n * 1 - d * 1) (s + (d + n) * 1 + (d - n) * 1))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) : False := by
  obtain ⟨i2, j2, hi2a, hi2b, hj2a, hj2b, hT2⟩ := hTop
  have hi2' : i2 = -1 ∨ i2 = 0 ∨ i2 = 1 := by omega
  have hj2' : j2 = -1 ∨ j2 = 0 ∨ j2 = 1 := by omega
  rcases hi2' with rfl | rfl | rfl <;> rcases hj2' with rfl | rfl | rfl <;>
    simp only [FHr, ClG, hSpG] at hB hT2
  · exact bot_key n d T (t + n * 1 - d * 1) (t + n * (-1) - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 1) (t + n * (-1) - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 1) (t + n * (-1) - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 1) (t + n * 0 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 1) (t + n * 0 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 1) (t + n * 0 - d * 1) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 1) (t + n * 1 - d * (-1)) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 1) (t + n * 1 - d * 0) hT3 (by omega) (by omega) (by omega)
  · exact bot_key n d T (t + n * 1 - d * 1) (t + n * 1 - d * 1) hT3 (by omega) (by omega) (by omega)

/-- **A bottom witness and a top-type neighbour cannot both occur (grade level).** -/
theorem bot_top_empty (n d T t s : Int) (hn : n % 2 = 1) (hd : d % 2 = 1) (hn1 : 1 ≤ n) (hnd : n + 2 ≤ d)
    (hT3 : 3 * (d + n) ≤ T)
    (hB : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j) (s + (d + n) * i + (d - n) * j))
    (hTop : ∃ i j : Int, -1 ≤ i ∧ i ≤ 1 ∧ -1 ≤ j ∧ j ≤ 1 ∧
      FHr n d T (t + n * i - d * j + T) (s + (d + n) * i + (d - n) * j)) : False := by
  obtain ⟨i1, j1, hi1a, hi1b, hj1a, hj1b, hB1⟩ := hB
  have hi1' : i1 = -1 ∨ i1 = 0 ∨ i1 = 1 := by omega
  have hj1' : j1 = -1 ∨ j1 = 0 ∨ j1 = 1 := by omega
  rcases hi1' with rfl | rfl | rfl <;> rcases hj1' with rfl | rfl | rfl
  · exact bot_top_mm n d T t s hn hd hn1 hnd hT3 hB1 hTop
  · exact bot_top_mz n d T t s hn hd hn1 hnd hT3 hB1 hTop
  · exact bot_top_mp n d T t s hn hd hn1 hnd hT3 hB1 hTop
  · exact bot_top_zm n d T t s hn hd hn1 hnd hT3 hB1 hTop
  · exact bot_top_zz n d T t s hn hd hn1 hnd hT3 hB1 hTop
  · exact bot_top_zp n d T t s hn hd hn1 hnd hT3 hB1 hTop
  · exact bot_top_pm n d T t s hn hd hn1 hnd hT3 hB1 hTop
  · exact bot_top_pz n d T t s hn hd hn1 hnd hT3 hB1 hTop
  · exact bot_top_pp n d T t s hn hd hn1 hnd hT3 hB1 hTop

end FLatticePaper.BottomTopEmpty
