import FLatticePaper.Tiles.SiteMaskStair

/-! Task 53, item 1: the near-one odd staircase `M3`, `nstairN (2k + 3) = H_{⟨k + 1, k + 2⟩}` for `k ≥ 0`.

`nstairN d` is `nstairF d` shifted by `(0, −1)`: its sites are the window `0 ≤ x ≤ d + 1`, `0 ≤ y ≤ 2d − 2`, `x − 2 ≤ y ≤ x + d − 1`
(the main part) together with the two corners `(0, d)` and `(d + 1, d − 2)`, which are on odd sites.

For `X = ⟨k + 1, k + 2⟩` the type is odd, `μ = 2`, `T = 2k² + 8k + 7`, `a = 1` on even sites and `k + 1` on odd sites,
`l = 0` on even sites and `1` on odd sites. With `t = (k+1)x − (k+2)y` and `s = (2k+3)x + y`. -/

namespace FLatticePaper.Tiles.SiteMaskNear3

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteMaskStair

theorem InH_n3_even (k x y : ℤ) (hk : 0 ≤ k) (hp : (x + y) % 2 = 0) :
    InH ⟨k + 1, k + 2⟩ (x, y) ↔
      (-2 * k ^ 2 - 8 * k - 6 ≤ (k + 1) * x - (k + 2) * y ∧ (k + 1) * x - (k + 2) * y ≤ 2 * k + 2 ∧
        0 ≤ (2 * k + 3) * x + y ∧ (2 * k + 3) * x + y ≤ 4 * k ^ 2 + 18 * k + 16) := by
  have hmu : muOf ⟨k + 1, k + 2⟩ = 2 := by unfold muOf; dsimp only; rw [if_pos (by omega)]
  have ha : aOf ⟨k + 1, k + 2⟩ true = 1 := by
    unfold aOf; rw [if_pos rfl]; dsimp only; omega
  have hl : lOf ⟨k + 1, k + 2⟩ true = 0 := by unfold lOf; rw [if_pos rfl]
  have hT : tOf ⟨k + 1, k + 2⟩ = 2 * k ^ 2 + 8 * k + 7 := by unfold tOf; ring
  unfold InH
  simp only [decide_eq_true hp, ha, hl, hmu, hT, tCo, sCo]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩

theorem InH_n3_odd (k x y : ℤ) (hk : 0 ≤ k) (hp : (x + y) % 2 ≠ 0) :
    InH ⟨k + 1, k + 2⟩ (x, y) ↔
      (-2 * k ^ 2 - 7 * k - 6 ≤ (k + 1) * x - (k + 2) * y ∧ (k + 1) * x - (k + 2) * y ≤ k + 2 ∧
        1 ≤ (2 * k + 3) * x + y ∧ (2 * k + 3) * x + y ≤ 4 * k ^ 2 + 18 * k + 15) := by
  have hmu : muOf ⟨k + 1, k + 2⟩ = 2 := by unfold muOf; dsimp only; rw [if_pos (by omega)]
  have ha : aOf ⟨k + 1, k + 2⟩ false = k + 1 := by unfold aOf; rw [if_neg (by simp)]
  have hl : lOf ⟨k + 1, k + 2⟩ false = 1 := by
    unfold lOf
    rw [if_neg (by simp)]
    dsimp only
    omega
  have hT : tOf ⟨k + 1, k + 2⟩ = 2 * k ^ 2 + 8 * k + 7 := by unfold tOf; ring
  unfold InH
  simp only [decide_eq_false hp, ha, hl, hmu, hT, tCo, sCo]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩

/-- The main part of `nstairN (2k + 3)` (before the corners), on even sites, is the even `H` set. -/
theorem main_even_fwd3 (k x y : ℤ) (hk : 0 ≤ k)
    (h1 : 0 ≤ x) (h2 : x ≤ 2 * k + 4) (h3 : 0 ≤ y) (h4 : y ≤ 4 * k + 4) (h5 : x - 2 ≤ y) (h6 : y ≤ x + 2 * k + 2) :
    -2 * k ^ 2 - 8 * k - 6 ≤ (k + 1) * x - (k + 2) * y ∧ (k + 1) * x - (k + 2) * y ≤ 2 * k + 2 ∧
      0 ≤ (2 * k + 3) * x + y ∧ (2 * k + 3) * x + y ≤ 4 * k ^ 2 + 18 * k + 16 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 1 by omega) (show (0 : ℤ) ≤ x + 2 * k + 2 - y by omega)]
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 1 by omega) (show (0 : ℤ) ≤ y - x + 2 by omega)]
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) h1]
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ 2 * k + 4 - x by omega)]

/-- The even `H` inequalities give the main part of `nstairN (2k + 3)`, on even sites. -/
theorem main_even_bwd3 (k x y : ℤ) (hk : 0 ≤ k) (hp : (x + y) % 2 = 0)
    (e1 : -2 * k ^ 2 - 8 * k - 6 ≤ (k + 1) * x - (k + 2) * y) (e2 : (k + 1) * x - (k + 2) * y ≤ 2 * k + 2)
    (e3 : 0 ≤ (2 * k + 3) * x + y) (e4 : (2 * k + 3) * x + y ≤ 4 * k ^ 2 + 18 * k + 16) :
    0 ≤ x ∧ x ≤ 2 * k + 4 ∧ 0 ≤ y ∧ y ≤ 4 * k + 4 ∧ x - 2 ≤ y ∧ y ≤ x + 2 * k + 2 := by
  have hx0 : 0 ≤ x := by
    by_contra hc
    have hc' : x ≤ -1 := by omega
    have hy2 : 2 * k + 3 ≤ y := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ -1 - x by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 2 by omega) (show (0 : ℤ) ≤ y - (2 * k + 3) by omega)]
  have hy0 : 0 ≤ y := by
    by_contra hc
    have hc' : y ≤ -1 := by omega
    have hx1 : 0 < x := by
      by_contra h
      push Not at h
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ -x by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 2 by omega) (show (0 : ℤ) ≤ -1 - y by omega)]
  have hx2 : x ≤ 2 * k + 4 := by
    by_contra hc
    have hc' : 2 * k + 5 ≤ x := by omega
    have hy1 : y ≤ 2 * k + 1 := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ x - (2 * k + 5) by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 2 by omega) (show (0 : ℤ) ≤ 2 * k + 1 - y by omega)]
  have hy4 : y ≤ 4 * k + 4 := by
    by_contra hc
    have hc' : 4 * k + 5 ≤ y := by omega
    have hx3 : x ≤ 2 * k + 3 := by
      by_contra h
      have h' : 2 * k + 4 ≤ x := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ x - (2 * k + 4) by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 2 by omega) (show (0 : ℤ) ≤ y - (4 * k + 5) by omega),
      mul_nonneg (show (0 : ℤ) ≤ k + 1 by omega) (show (0 : ℤ) ≤ 2 * k + 3 - x by omega)]
  have hlo : x - 2 ≤ y := by
    by_contra hc
    have hc' : y + 4 ≤ x := by
      have : x - y ≥ 3 := by omega
      have : x - y ≠ 3 := by
        intro h
        have : x + y = 2 * y + 3 := by omega
        omega
      omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 4 by omega) (show (0 : ℤ) ≤ 2 * k + 2 - ((k + 1) * x - (k + 2) * y) by linarith),
      mul_nonneg (show (0 : ℤ) ≤ 2 * k + 4 by omega) (show (0 : ℤ) ≤ 4 * k ^ 2 + 18 * k + 16 - ((2 * k + 3) * x + y) by linarith),
      mul_nonneg (show (0 : ℤ) ≤ 2 * k ^ 2 + 8 * k + 7 by nlinarith) (show (0 : ℤ) ≤ x - y - 4 by omega)]
  have hhi : y ≤ x + 2 * k + 2 := by
    by_contra hc
    have hc' : x + 2 * k + 4 ≤ y := by
      have : y - x ≥ 2 * k + 3 := by omega
      have : y - x ≠ 2 * k + 3 := by
        intro h
        have : x + y = 2 * x + 2 * k + 3 := by omega
        omega
      omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 2 by omega) (show (0 : ℤ) ≤ y - x - (2 * k + 4) by omega)]
  exact ⟨hx0, hx2, hy0, hy4, hlo, hhi⟩

/-- The main part of `nstairN (2k + 3)` on odd sites is in the odd `H` set. -/
theorem main_odd_fwd3 (k x y : ℤ) (hk : 0 ≤ k) (hp : (x + y) % 2 ≠ 0)
    (h1 : 0 ≤ x) (h2 : x ≤ 2 * k + 4) (h3 : 0 ≤ y) (h4 : y ≤ 4 * k + 4) (h5 : x - 2 ≤ y) (h6 : y ≤ x + 2 * k + 2) :
    -2 * k ^ 2 - 7 * k - 6 ≤ (k + 1) * x - (k + 2) * y ∧ (k + 1) * x - (k + 2) * y ≤ k + 2 ∧
      1 ≤ (2 * k + 3) * x + y ∧ (2 * k + 3) * x + y ≤ 4 * k ^ 2 + 18 * k + 15 := by
  have hsplit : (2 * k + 3) * x + y = 2 * (k * x + x) + (x + y) := by ring
  have hbound : 4 * k ^ 2 + 18 * k + 16 = 2 * (2 * k ^ 2 + 9 * k + 8) := by ring
  have hv1 : 1 ≤ x + 2 * k + 2 - y := by omega
  have hy1 : x - 1 ≤ y := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 1 by omega) (show (0 : ℤ) ≤ x + 2 * k + 2 - y - 1 by omega)]
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 1 by omega) (show (0 : ℤ) ≤ y - x + 1 by omega)]
  · have hnn : 0 ≤ (2 * k + 3) * x + y := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) h1]
    omega
  · have hle : (2 * k + 3) * x + y ≤ 4 * k ^ 2 + 18 * k + 16 := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ 2 * k + 4 - x by omega)]
    omega

/-- The odd `H` inequalities give the main part of `nstairN (2k + 3)` or one of its corners, on odd sites. -/
theorem main_odd_bwd3 (k x y : ℤ) (hk : 0 ≤ k)
    (o1 : -2 * k ^ 2 - 7 * k - 6 ≤ (k + 1) * x - (k + 2) * y) (o2 : (k + 1) * x - (k + 2) * y ≤ k + 2)
    (o3 : 1 ≤ (2 * k + 3) * x + y) (o4 : (2 * k + 3) * x + y ≤ 4 * k ^ 2 + 18 * k + 15) :
    (0 ≤ x ∧ x ≤ 2 * k + 4 ∧ 0 ≤ y ∧ y ≤ 4 * k + 4 ∧ x - 2 ≤ y ∧ y ≤ x + 2 * k + 2) ∨
      (x = 0 ∧ y = 2 * k + 3) ∨ (x = 2 * k + 4 ∧ y = 2 * k + 1) := by
  have hy0 : 0 ≤ y := by
    by_contra hc
    have hc' : y ≤ -1 := by omega
    have hx1 : 1 ≤ x := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ 0 by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 2 by omega) (show (0 : ℤ) ≤ -1 - y by omega)]
  have hx0 : 0 ≤ x := by
    by_contra hc
    have hc' : x ≤ -1 := by omega
    have hy2 : 2 * k + 4 ≤ y := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ -1 - x by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 2 by omega) (show (0 : ℤ) ≤ y - (2 * k + 4) by omega)]
  have hx2 : x ≤ 2 * k + 4 := by
    by_contra hc
    have hc' : 2 * k + 5 ≤ x := by omega
    have hy1 : y ≤ 2 * k := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ x - (2 * k + 5) by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 2 by omega) (show (0 : ℤ) ≤ 2 * k - y by omega)]
  have hy4 : y ≤ 4 * k + 4 := by
    by_contra hc
    have hc' : 4 * k + 5 ≤ y := by omega
    have hx3 : x ≤ 2 * k + 3 := by
      by_contra h
      have h' : 2 * k + 4 ≤ x := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ x - (2 * k + 4) by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 2 by omega) (show (0 : ℤ) ≤ y - (4 * k + 5) by omega),
      mul_nonneg (show (0 : ℤ) ≤ k + 1 by omega) (show (0 : ℤ) ≤ 2 * k + 3 - x by omega)]
  by_cases hc2 : x = 2 * k + 4 ∧ y = 2 * k + 1
  · exact Or.inr (Or.inr hc2)
  by_cases hc1 : x = 0 ∧ y = 2 * k + 3
  · exact Or.inr (Or.inl hc1)
  have hlo : x - 2 ≤ y := by
    by_contra hc
    have hd3 : x - y ≥ 3 := by omega
    have hy' : 2 * k + 1 ≤ y := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ k + 1 by omega) (show (0 : ℤ) ≤ x - y - 3 by omega)]
    have hxe : x = 2 * k + 4 := by omega
    have hye : y = 2 * k + 1 := by omega
    exact absurd ⟨hxe, hye⟩ hc2
  have hhi : y ≤ x + 2 * k + 2 := by
    by_contra hc
    have hc' : x + 2 * k + 3 ≤ y := by omega
    have hx0' : x = 0 := by nlinarith
    have hy' : y ≤ 2 * k + 3 := by nlinarith
    have hye : y = 2 * k + 3 := by omega
    exact absurd ⟨hx0', hye⟩ hc1
  exact Or.inl ⟨hx0, hx2, hy0, hy4, hlo, hhi⟩

/-- The two corners of `nstairN (2k + 3)` are in the odd `H` set. -/
theorem corners_odd3 (k : ℤ) (hk : 0 ≤ k) :
    (-2 * k ^ 2 - 7 * k - 6 ≤ (k + 1) * 0 - (k + 2) * (2 * k + 3) ∧ (k + 1) * 0 - (k + 2) * (2 * k + 3) ≤ k + 2 ∧
      1 ≤ (2 * k + 3) * 0 + (2 * k + 3) ∧ (2 * k + 3) * 0 + (2 * k + 3) ≤ 4 * k ^ 2 + 18 * k + 15) ∧
    (-2 * k ^ 2 - 7 * k - 6 ≤ (k + 1) * (2 * k + 4) - (k + 2) * (2 * k + 1) ∧
      (k + 1) * (2 * k + 4) - (k + 2) * (2 * k + 1) ≤ k + 2 ∧
      1 ≤ (2 * k + 3) * (2 * k + 4) + (2 * k + 1) ∧ (2 * k + 3) * (2 * k + 4) + (2 * k + 1) ≤ 4 * k ^ 2 + 18 * k + 15) := by
  constructor
  · refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- A site is in `nstairN d` when the site shifted by `(0, 1)` is in `nstairF d`. -/
theorem mem_nstairN_iff (d x y : ℤ) : (x, y) ∈ nstairN d ↔ (x, y + 1) ∈ nstairF d := by
  unfold nstairN shift
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨a, b⟩, hab, heq⟩
    simp only [Prod.mk_add_mk, Prod.mk.injEq] at heq
    obtain ⟨h1, h2⟩ := heq
    have ha : a = x := by linarith
    have hb : b = y + 1 := by linarith
    subst ha
    subst hb
    exact hab
  · intro h
    exact ⟨(x, y + 1), h, by ext <;> simp⟩

/-- The window of `nstairN (2k + 3)`: the main part and the two corners. -/
theorem nstairN_window (k x y : ℤ) (hk : 0 ≤ k) :
    (x, y) ∈ nstairN (2 * k + 3) ↔
      (0 ≤ x ∧ x ≤ 2 * k + 4 ∧ 0 ≤ y ∧ y ≤ 4 * k + 4 ∧ x - 2 ≤ y ∧ y ≤ x + 2 * k + 2) ∨
        (x = 0 ∧ y = 2 * k + 3) ∨ (x = 2 * k + 4 ∧ y = 2 * k + 1) := by
  rw [mem_nstairN_iff, mem_nstairF (by omega : (2 : ℤ) ≤ 2 * k + 3)]
  dsimp only
  constructor
  · intro h
    omega
  · intro h
    omega

/-- `M3`: the near-one odd staircase `nstairN (2k + 3)` is the set `H_X` of its fraction `⟨k + 1, k + 2⟩`. -/
theorem nstair_eq3 (k : ℤ) (hk : 0 ≤ k) :
    ((nstairN (2 * k + 3) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet ⟨k + 1, k + 2⟩ := by
  ext ⟨x, y⟩
  rw [Finset.mem_coe, nstairN_window k x y hk]
  show _ ↔ InH ⟨k + 1, k + 2⟩ (x, y)
  by_cases hp : (x + y) % 2 = 0
  · rw [InH_n3_even k x y hk hp]
    constructor
    · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact main_even_fwd3 k x y hk h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
      · exfalso
        omega
      · exfalso
        omega
    · intro h
      obtain ⟨h0, h2, h3, h4, h5, h6⟩ := main_even_bwd3 k x y hk hp h.1 h.2.1 h.2.2.1 h.2.2.2
      exact Or.inl ⟨h0, h2, h3, h4, h5, h6⟩
  · rw [InH_n3_odd k x y hk hp]
    constructor
    · rintro (⟨h0, h2, h3, h4, h5, h6⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact main_odd_fwd3 k x y hk hp h0 h2 h3 h4 h5 h6
      · subst h1
        subst h2
        exact (corners_odd3 k hk).1
      · subst h1
        subst h2
        exact (corners_odd3 k hk).2
    · intro h
      rcases main_odd_bwd3 k x y hk h.1 h.2.1 h.2.2.1 h.2.2.2 with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')

end FLatticePaper.Tiles.SiteMaskNear3
