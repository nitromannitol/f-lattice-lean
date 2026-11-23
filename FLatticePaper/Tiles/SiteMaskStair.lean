import FLatticePaper.Tiles.SiteBase

/-! Task 53, item 1: the even staircase `M1`, `stairF d = H_{⟨1, d⟩}` for odd `d ≥ 3`.

For `X = ⟨1, d⟩` the type is even (`d + 1` even), so `μ = 1`, `T = d² + 2d − 1`, `a = 2` on even sites and `1` on odd sites
(`min (2, d − 1) = 2`), `l = 0` on even sites and `3 − d` on odd sites (`min (d − 1, 3 − d) = 3 − d`). The two parity classes give
the explicit inequalities of `InH_one_even` and `InH_one_odd`. -/

namespace FLatticePaper.Tiles.SiteMaskStair

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SiteInduction

theorem InH_one_even (d x y : ℤ) (hd : 3 ≤ d) (hdo : d % 2 = 1) (hp : (x + y) % 2 = 0) :
    InH ⟨1, d⟩ (x, y) ↔
      (3 - d ^ 2 - 2 * d ≤ x - d * y ∧ x - d * y ≤ d - 1 ∧
        0 ≤ (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y ≤ (d + 1) ^ 2) := by
  have hmu : muOf ⟨1, d⟩ = 1 := by unfold muOf; dsimp only; rw [if_neg (by omega)]
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

theorem InH_one_odd (d x y : ℤ) (hd : 3 ≤ d) (hdo : d % 2 = 1) (hp : (x + y) % 2 ≠ 0) :
    InH ⟨1, d⟩ (x, y) ↔
      (2 - d ^ 2 - 2 * d ≤ x - d * y ∧ x - d * y ≤ d ∧
        3 - d ≤ (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y ≤ d ^ 2 + 3 * d - 2) := by
  have hmu : muOf ⟨1, d⟩ = 1 := by unfold muOf; dsimp only; rw [if_neg (by omega)]
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

/-- The staircase membership on even sites. -/
theorem stair_even_iff (d x y : ℤ) (hd : 3 ≤ d) (hdo : d % 2 = 1) (hp : (x + y) % 2 = 0) :
    ((2 - d ≤ x ∧ x ≤ d ∧ 0 ≤ y ∧ y ≤ d + 1 ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) ∨ (x = 0 ∧ y = 0) ∨ (x = 2 ∧ y = d + 1)) ↔
      (3 - d ^ 2 - 2 * d ≤ x - d * y ∧ x - d * y ≤ d - 1 ∧
        0 ≤ (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y ≤ (d + 1) ^ 2) := by
  constructor
  · rintro (⟨h1, h2, h3, h4, h5, h6⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have hA : d * y ≤ d * (d + 1) := by nlinarith
      have hB : 2 ≤ x + y := by omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · by_contra hc
        push Not at hc
        have hx : x = 2 - d := by nlinarith
        have hy : y = d + 1 := by nlinarith
        omega
      · rcases (show y = 0 ∨ 1 ≤ y by omega) with hy0 | hy1
        · subst hy0
          simp only [mul_zero, sub_zero]
          omega
        · nlinarith
      · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ x + y - 2 by omega)]
      · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ d + 1 - (x + y) by omega)]
    · refine ⟨by nlinarith, by omega, by norm_num, by simp only [mul_zero, add_zero]; positivity⟩
    · refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hy0 : 0 ≤ y := by
      by_contra hc
      have hc' : y ≤ -1 := by omega
      nlinarith
    have hyd : y ≤ d + 1 := by
      by_contra hc
      have hc' : d + 2 ≤ y := by omega
      nlinarith
    have hxd : x ≤ d := by
      by_contra hc
      have hc' : d + 1 ≤ x := by omega
      have hy' : y ≤ 0 := by nlinarith
      have hy'' : y = 0 := by omega
      subst hy''
      simp only [mul_zero, sub_zero] at h2
      omega
    have hxl : 2 - d ≤ x := by
      by_contra hc
      have hc' : x ≤ 1 - d := by omega
      have hy' : d + 1 ≤ y := by nlinarith
      nlinarith
    by_cases hs : 1 ≤ x + y
    · by_cases hs2 : x + y ≤ d + 2
      · exact Or.inl ⟨hxl, hxd, hy0, hyd, hs, hs2⟩
      · have hS : d + 3 ≤ x + y := by omega
        have hx2 : x ≤ 2 := by nlinarith
        by_cases hx1 : x ≤ 1
        · omega
        · have hx2' : x = 2 := by omega
          subst hx2'
          exact Or.inr (Or.inr ⟨rfl, by omega⟩)
    · have hsz : x + y ≤ 0 := by omega
      have hx0 : 0 ≤ x := by nlinarith
      have hx0' : x = 0 := by omega
      subst hx0'
      have hy00 : y = 0 := by omega
      exact Or.inr (Or.inl ⟨rfl, hy00⟩)

/-- The staircase membership on odd sites. -/
theorem stair_odd_iff (d x y : ℤ) (hd : 3 ≤ d) (hdo : d % 2 = 1) (hp : (x + y) % 2 ≠ 0) :
    ((2 - d ≤ x ∧ x ≤ d ∧ 0 ≤ y ∧ y ≤ d + 1 ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) ∨ (x = 0 ∧ y = 0) ∨ (x = 2 ∧ y = d + 1)) ↔
      (2 - d ^ 2 - 2 * d ≤ x - d * y ∧ x - d * y ≤ d ∧
        3 - d ≤ (d + 1) * x + (d - 1) * y ∧ (d + 1) * x + (d - 1) * y ≤ d ^ 2 + 3 * d - 2) := by
  constructor
  · rintro (⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h, h'⟩ | ⟨h, h'⟩)
    · have hA : d * y ≤ d * (d + 1) := by nlinarith
      refine ⟨by nlinarith, by nlinarith, by nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ x + y - 1 by omega)], by nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 1 by omega) (show (0 : ℤ) ≤ d + 2 - (x + y) by omega)]⟩
    · exact absurd (by omega) hp
    · exact absurd (by omega) hp
  · rintro ⟨h1, h2, h3, h4⟩
    have hy0 : 0 ≤ y := by
      by_contra hc
      have hc' : y ≤ -1 := by omega
      nlinarith
    have hyd : y ≤ d + 1 := by
      by_contra hc
      have hc' : d + 2 ≤ y := by omega
      nlinarith
    have hxd : x ≤ d := by
      by_contra hc
      have hc' : d + 1 ≤ x := by omega
      have hy' : y ≤ 0 := by nlinarith
      have hy'' : y = 0 := by omega
      subst hy''
      simp only [mul_zero, sub_zero] at h2
      omega
    have hxl : 2 - d ≤ x := by
      by_contra hc
      have hc' : x ≤ 1 - d := by omega
      have hy' : d + 1 ≤ y := by nlinarith
      nlinarith
    have hs : 1 ≤ x + y := by
      by_contra hc
      have hc' : x + y ≤ -1 := by omega
      have hx1 : 1 ≤ x := by nlinarith
      omega
    have hs2 : x + y ≤ d + 2 := by
      by_contra hc
      have hc' : d + 4 ≤ x + y := by omega
      have hx1 : x ≤ 1 := by nlinarith
      have hx3 : 3 ≤ x := by omega
      omega
    exact Or.inl ⟨hxl, hxd, hy0, hyd, hs, hs2⟩

theorem stair_iff (d x y : ℤ) (hd : 3 ≤ d) (hdo : d % 2 = 1) :
    ((2 - d ≤ x ∧ x ≤ d ∧ 0 ≤ y ∧ y ≤ d + 1 ∧ 1 ≤ x + y ∧ x + y ≤ d + 2) ∨ (x = 0 ∧ y = 0) ∨ (x = 2 ∧ y = d + 1)) ↔
      InH ⟨1, d⟩ (x, y) := by
  by_cases hp : (x + y) % 2 = 0
  · rw [InH_one_even d x y hd hdo hp]
    exact stair_even_iff d x y hd hdo hp
  · rw [InH_one_odd d x y hd hdo hp]
    exact stair_odd_iff d x y hd hdo hp

/-- `M1`: the even staircase `stairF (2k + 3)` is the set `H_X` of its fraction `⟨1, 2k + 3⟩`. -/
theorem stair_eq (k : ℕ) :
    ((stairF (2 * (k : ℤ) + 3) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet ⟨1, 2 * (k : ℤ) + 3⟩ := by
  ext z
  obtain ⟨x, y⟩ := z
  rw [Finset.mem_coe, mem_stairF (by omega : (2 : ℤ) ≤ 2 * (k : ℤ) + 3)]
  exact stair_iff _ x y (by omega) (by omega)

end FLatticePaper.Tiles.SiteMaskStair
