import FLatticePaper.Tiles.SiteMaskStair

/-! Task 53, item 1: the odd doubled ladder `M2`, `ladderF b = H_{⟨1, b⟩}` for even `b ≥ 4`.

For `X = ⟨1, b⟩` the type is odd (`b + 1` odd), so `μ = 2`, `T = b² + 2b − 1`, `a = 2` on even sites and `1` on odd sites,
`l = 0` on even sites and `3 − b` on odd sites. The membership of `ladderF b` is the window with the two corners and the two deleted
edge strips (`mem_ladderF`). Corners and the diagonal `x + y = b + 2` are on even sites only (`b` even). -/

namespace FLatticePaper.Tiles.SiteMaskLadder

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteMaskStair

theorem InH_ladder_even (d x y : ℤ) (hd : 4 ≤ d) (hde : d % 2 = 0) (hp : (x + y) % 2 = 0) :
    InH ⟨1, d⟩ (x, y) ↔
      (3 - d ^ 2 - 2 * d ≤ x - d * y ∧ x - d * y ≤ d - 1 ∧
        0 ≤ (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y ≤ 2 * (d ^ 2 + 2 * d - 1) + 2) := by
  have hmu : muOf ⟨1, d⟩ = 2 := by unfold muOf; dsimp only; rw [if_pos (by omega)]
  have ha : aOf ⟨1, d⟩ true = 2 := by unfold aOf; rw [if_pos rfl]; dsimp only; omega
  have hl : lOf ⟨1, d⟩ true = 0 := by unfold lOf; rw [if_pos rfl]
  have hT : tOf ⟨1, d⟩ = d ^ 2 + 2 * d - 1 := by unfold tOf; ring
  unfold InH
  simp only [decide_eq_true hp, ha, hl, hmu, hT, tCo, sCo]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩

theorem InH_ladder_odd (d x y : ℤ) (hd : 4 ≤ d) (hde : d % 2 = 0) (hp : (x + y) % 2 ≠ 0) :
    InH ⟨1, d⟩ (x, y) ↔
      (2 - d ^ 2 - 2 * d ≤ x - d * y ∧ x - d * y ≤ d ∧
        3 - d ≤ (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y ≤ 2 * d ^ 2 + 5 * d - 3) := by
  have hmu : muOf ⟨1, d⟩ = 2 := by unfold muOf; dsimp only; rw [if_pos (by omega)]
  have ha : aOf ⟨1, d⟩ false = 1 := by unfold aOf; rw [if_neg (by simp)]
  have hl : lOf ⟨1, d⟩ false = 3 - d := by
    unfold lOf
    rw [if_neg (by simp)]
    dsimp only
    omega
  have hT : tOf ⟨1, d⟩ = d ^ 2 + 2 * d - 1 := by unfold tOf; ring
  unfold InH
  simp only [decide_eq_false hp, ha, hl, hmu, hT, tCo, sCo]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩

/-- The main window of `ladderF`, on even sites, implies the even `H` inequalities. -/
theorem main_even_fwd (d x y : ℤ) (hd : 4 ≤ d) (hde : d % 2 = 0) (hp : (x + y) % 2 = 0)
    (h1 : 2 - d ≤ x) (h2 : x ≤ 2 * d) (h3 : 0 ≤ y) (h4 : y ≤ d + 2) (h5 : 1 ≤ x + y) (h6 : x + y ≤ 2 * d + 3)
    (hB : ¬((d ≤ x ∧ y = 0) ∨ (x ≤ 2 ∧ y = d + 2))) :
    3 - d ^ 2 - 2 * d ≤ x - d * y ∧ x - d * y ≤ d - 1 ∧
      0 ≤ (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y ≤ 2 * (d ^ 2 + 2 * d - 1) + 2 := by
  have hA : d * y ≤ d * (d + 2) := by nlinarith
  have hS2 : 2 ≤ x + y := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    have hy : d + 1 ≤ y := by nlinarith
    rcases (show y = d + 1 ∨ y = d + 2 by omega) with rfl | rfl
    · have hx : x = 2 - d := by nlinarith
      omega
    · have hx : x ≤ 2 := by nlinarith
      exact hB (Or.inr ⟨hx, rfl⟩)
  · rcases (show y = 0 ∨ y = 1 ∨ 2 ≤ y by omega) with rfl | rfl | hy2
    · have hxd : ¬ (d ≤ x) := fun h => hB (Or.inl ⟨h, rfl⟩)
      simp only [mul_zero, sub_zero]
      omega
    · simp only [mul_one]
      omega
    · nlinarith
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ x + y - 2 by omega)]
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ 2 * d + 2 - (x + y) by omega)]

/-- The main window of `ladderF`, on odd sites, implies the odd `H` inequalities. -/
theorem main_odd_fwd (d x y : ℤ) (hd : 4 ≤ d) (hde : d % 2 = 0) (hp : (x + y) % 2 ≠ 0)
    (h1 : 2 - d ≤ x) (h2 : x ≤ 2 * d) (h3 : 0 ≤ y) (h4 : y ≤ d + 2) (h5 : 1 ≤ x + y) (h6 : x + y ≤ 2 * d + 3)
    (hB : ¬((d ≤ x ∧ y = 0) ∨ (x ≤ 2 ∧ y = d + 2))) :
    2 - d ^ 2 - 2 * d ≤ x - d * y ∧ x - d * y ≤ d ∧
      3 - d ≤ (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y ≤ 2 * d ^ 2 + 5 * d - 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hc
    push Not at hc
    have hy : d + 2 ≤ y := by nlinarith
    have hy' : y = d + 2 := by omega
    subst hy'
    have hx : x ≤ 2 := by nlinarith
    exact hB (Or.inr ⟨hx, rfl⟩)
  · rcases (show y = 0 ∨ 1 ≤ y by omega) with rfl | hy1
    · have hxd : ¬ (d ≤ x) := fun h => hB (Or.inl ⟨h, rfl⟩)
      simp only [mul_zero, sub_zero]
      omega
    · nlinarith
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ x + y - 1 by omega)]
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ 2 * d + 3 - (x + y) by omega)]

/-- The even `H` inequalities give the window of `ladderF`, on even sites. -/
theorem ladder_even_bwd (d x y : ℤ) (hd : 4 ≤ d) (hde : d % 2 = 0) (hp : (x + y) % 2 = 0)
    (h1 : 3 - d ^ 2 - 2 * d ≤ x - d * y) (h2 : x - d * y ≤ d - 1)
    (h3 : 0 ≤ (d + 1) * x + (d - 1) * y) (h4 : (d + 1) * x + (d - 1) * y ≤ 2 * (d ^ 2 + 2 * d - 1) + 2) :
    ((x = 0 ∧ y = 0) ∨ (x = d + 2 ∧ y = d + 2) ∨ (x + y = d + 2 ∧ 1 < y ∧ y < d + 1) ∨
      (2 - d ≤ x ∧ x ≤ 2 * d ∧ 0 ≤ y ∧ y ≤ d + 2 ∧ 1 ≤ x + y ∧ x + y ≤ 2 * d + 3)) ∧
    ¬((d ≤ x ∧ y = 0) ∨ (x ≤ 2 ∧ y = d + 2)) := by
  have hy0 : 0 ≤ y := by
    by_contra hc
    have hc' : y ≤ -1 := by omega
    have hx1 : 1 ≤ x := by nlinarith
    nlinarith
  have hyd : y ≤ d + 2 := by
    by_contra hc
    have hc' : d + 3 ≤ y := by omega
    have hx3 : d + 3 ≤ x := by nlinarith
    nlinarith
  by_cases hS : 1 ≤ x + y
  · by_cases hS2 : x + y ≤ 2 * d + 3
    · have hx1 : 2 - d ≤ x := by
        by_contra hc
        have hc' : x ≤ 1 - d := by omega
        have hy1 : d + 1 ≤ y := by nlinarith
        nlinarith
      have hx2 : x ≤ 2 * d := by
        by_contra hc
        have hc' : 2 * d + 1 ≤ x := by omega
        have hy1 : y ≤ 1 := by nlinarith
        nlinarith
      have hB : ¬((d ≤ x ∧ y = 0) ∨ (x ≤ 2 ∧ y = d + 2)) := by
        rintro (⟨h5, h6⟩ | ⟨h5, h6⟩)
        · subst h6
          simp only [mul_zero, sub_zero] at h2
          omega
        · subst h6
          have : 3 ≤ x := by nlinarith
          omega
      exact ⟨Or.inr (Or.inr (Or.inr ⟨hx1, hx2, hy0, hyd, hS, hS2⟩)), hB⟩
    · have hS3 : 2 * d + 4 ≤ x + y := by omega
      have hx : x ≤ d + 2 := by
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ x + y - (2 * d + 4) by omega)]
      have hxe : x = d + 2 := by omega
      have hye : y = d + 2 := by omega
      exact ⟨Or.inr (Or.inl ⟨hxe, hye⟩), by omega⟩
  · have hS0 : x + y ≤ 0 := by omega
    have hx0 : 0 ≤ x := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ -(x + y) by omega)]
    have hxz : x = 0 := by omega
    have hyz : y = 0 := by omega
    exact ⟨Or.inl ⟨hxz, hyz⟩, by omega⟩

/-- The odd `H` inequalities give the window of `ladderF`, on odd sites. -/
theorem ladder_odd_bwd (d x y : ℤ) (hd : 4 ≤ d) (hde : d % 2 = 0) (hp : (x + y) % 2 ≠ 0)
    (h1 : 2 - d ^ 2 - 2 * d ≤ x - d * y) (h2 : x - d * y ≤ d)
    (h3 : 3 - d ≤ (d + 1) * x + (d - 1) * y) (h4 : (d + 1) * x + (d - 1) * y ≤ 2 * d ^ 2 + 5 * d - 3) :
    ((x = 0 ∧ y = 0) ∨ (x = d + 2 ∧ y = d + 2) ∨ (x + y = d + 2 ∧ 1 < y ∧ y < d + 1) ∨
      (2 - d ≤ x ∧ x ≤ 2 * d ∧ 0 ≤ y ∧ y ≤ d + 2 ∧ 1 ≤ x + y ∧ x + y ≤ 2 * d + 3)) ∧
    ¬((d ≤ x ∧ y = 0) ∨ (x ≤ 2 ∧ y = d + 2)) := by
  have hy0 : 0 ≤ y := by
    by_contra hc
    have hc' : y ≤ -1 := by omega
    have hx1 : 1 ≤ x := by nlinarith
    nlinarith
  have hyd : y ≤ d + 2 := by
    by_contra hc
    have hc' : d + 3 ≤ y := by omega
    have hx2 : d + 2 ≤ x := by nlinarith
    nlinarith
  have hs : 1 ≤ x + y := by
    by_contra hc
    have hc' : x + y ≤ -1 := by omega
    have hx1 : 1 ≤ x := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ -1 - (x + y) by omega)]
    omega
  have hs2 : x + y ≤ 2 * d + 3 := by
    by_contra hc
    have hc' : 2 * d + 5 ≤ x + y := by omega
    have hx1 : x ≤ d + 1 := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ x + y - (2 * d + 5) by omega)]
    omega
  have hx1 : 2 - d ≤ x := by
    by_contra hc
    have hc' : x ≤ 1 - d := by omega
    have hy1 : d + 1 ≤ y := by nlinarith
    nlinarith
  have hx2 : x ≤ 2 * d := by
    by_contra hc
    have hc' : 2 * d + 1 ≤ x := by omega
    have hy1 : y ≤ 1 := by nlinarith
    nlinarith
  have hB : ¬((d ≤ x ∧ y = 0) ∨ (x ≤ 2 ∧ y = d + 2)) := by
    rintro (⟨h5, h6⟩ | ⟨h5, h6⟩)
    · subst h6
      simp only [mul_zero, sub_zero] at h2
      omega
    · subst h6
      have : 2 ≤ x := by nlinarith
      omega
  exact ⟨Or.inr (Or.inr (Or.inr ⟨hx1, hx2, hy0, hyd, hs, hs2⟩)), hB⟩

/-- `ladderF` on even sites is the even `H` set. -/
theorem ladder_even_iff (d x y : ℤ) (hd : 4 ≤ d) (hde : d % 2 = 0) (hp : (x + y) % 2 = 0) :
    ((x = 0 ∧ y = 0) ∨ (x = d + 2 ∧ y = d + 2) ∨ (x + y = d + 2 ∧ 1 < y ∧ y < d + 1) ∨
      (2 - d ≤ x ∧ x ≤ 2 * d ∧ 0 ≤ y ∧ y ≤ d + 2 ∧ 1 ≤ x + y ∧ x + y ≤ 2 * d + 3)) ∧
    ¬((d ≤ x ∧ y = 0) ∨ (x ≤ 2 ∧ y = d + 2)) ↔
      (3 - d ^ 2 - 2 * d ≤ x - d * y ∧ x - d * y ≤ d - 1 ∧
        0 ≤ (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y ≤ 2 * (d ^ 2 + 2 * d - 1) + 2) := by
  constructor
  · rintro ⟨hA, hB⟩
    rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hs, hy1, hy2⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
    · refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
    · refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
    · exact main_even_fwd d x y hd hde hp (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hB
    · exact main_even_fwd d x y hd hde hp h1 h2 h3 h4 h5 h6 hB
  · rintro ⟨h1, h2, h3, h4⟩
    exact ladder_even_bwd d x y hd hde hp h1 h2 h3 h4

/-- `ladderF` on odd sites is the odd `H` set (the corners and the diagonal are on even sites). -/
theorem ladder_odd_iff (d x y : ℤ) (hd : 4 ≤ d) (hde : d % 2 = 0) (hp : (x + y) % 2 ≠ 0) :
    ((x = 0 ∧ y = 0) ∨ (x = d + 2 ∧ y = d + 2) ∨ (x + y = d + 2 ∧ 1 < y ∧ y < d + 1) ∨
      (2 - d ≤ x ∧ x ≤ 2 * d ∧ 0 ≤ y ∧ y ≤ d + 2 ∧ 1 ≤ x + y ∧ x + y ≤ 2 * d + 3)) ∧
    ¬((d ≤ x ∧ y = 0) ∨ (x ≤ 2 ∧ y = d + 2)) ↔
      (2 - d ^ 2 - 2 * d ≤ x - d * y ∧ x - d * y ≤ d ∧
        3 - d ≤ (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y ≤ 2 * d ^ 2 + 5 * d - 3) := by
  constructor
  · rintro ⟨hA, hB⟩
    rcases hA with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hs, hy1, hy2⟩ | ⟨h1, h2, h3, h4, h5, h6⟩
    · exact absurd (by norm_num) hp
    · exact absurd (by omega) hp
    · exact absurd (by omega) hp
    · exact main_odd_fwd d x y hd hde hp h1 h2 h3 h4 h5 h6 hB
  · rintro ⟨h1, h2, h3, h4⟩
    exact ladder_odd_bwd d x y hd hde hp h1 h2 h3 h4

/-- `M2`: the odd doubled ladder `ladderF (2k + 2)` is the set `H_X` of its fraction `⟨1, 2k + 2⟩`, for `k ≥ 1`. -/
theorem ladder_eq (k : ℕ) (hk : 1 ≤ k) :
    ((ladderF (2 * (k : ℤ) + 2) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet ⟨1, 2 * (k : ℤ) + 2⟩ := by
  ext z
  obtain ⟨x, y⟩ := z
  have hk' : (4 : ℤ) ≤ 2 * (k : ℤ) + 2 := by omega
  have hde : (2 * (k : ℤ) + 2) % 2 = 0 := by omega
  rw [Finset.mem_coe, mem_ladderF (by omega : (2 : ℤ) ≤ 2 * (k : ℤ) + 2)]
  by_cases hp : (x + y) % 2 = 0
  · exact (ladder_even_iff _ x y hk' hde hp).trans (InH_ladder_even _ x y hk' hde hp).symm
  · exact (ladder_odd_iff _ x y hk' hde hp).trans (InH_ladder_odd _ x y hk' hde hp).symm

end FLatticePaper.Tiles.SiteMaskLadder
