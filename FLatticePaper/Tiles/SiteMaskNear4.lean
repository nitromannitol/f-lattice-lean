import FLatticePaper.Tiles.SiteMaskStair
import FLatticePaper.Tiles.SiteCoversNear

/-! Task 53, item 1: the near-one even doubled ladder `M4`, `nladderN (2k + 2) = H_{⟨2k + 1, 2k + 3⟩}` for `k ≥ 1`.

Window: with `d = 2k + 2` and the shift `(0, −1)` of `nladderN`, the sites are `Apart ∨ Bpart ∨ Cpart ∨ Dpart`, minus the exclusions
`Excl`. For `X = ⟨2k + 1, 2k + 3⟩` the type is even: `μ = 1`, `T = 8k² + 24k + 14`, `t = (2k+1) x − (2k+3) y`, `s = (4k+4) x + 2 y`;
on even sites `a = 2`, `l = 0`; on odd sites `a = 2k + 1`, `l = 2` (for `k ≥ 1`). -/

namespace FLatticePaper.Tiles.SiteMaskNear4

open FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.SiteMaskStair

def Dpart (k x y : ℤ) : Prop := -1 ≤ x ∧ x ≤ 2 * k + 3 ∧ 0 ≤ y ∧ y ≤ 6 * k + 4 ∧ -2 ≤ y - x ∧ y - x ≤ 4 * k + 4
def Apart (k x y : ℤ) : Prop := x = -1 ∧ y = 4 * k + 4
def Bpart (k x y : ℤ) : Prop := x = 2 * k + 3 ∧ y = 2 * k
def Cpart (k x y : ℤ) : Prop := y = x + 2 * k + 1 ∧ 0 < x ∧ x < 2 * k + 2
def Excl (k x y : ℤ) : Prop := (x = -1 ∧ y ≤ 2 * k + 2) ∨ (x = 2 * k + 3 ∧ 4 * k + 2 ≤ y)
def WinN4 (k x y : ℤ) : Prop := (Apart k x y ∨ Bpart k x y ∨ Cpart k x y ∨ Dpart k x y) ∧ ¬ Excl k x y

theorem nladder_window (k x y : ℤ) (hk : 1 ≤ k) : (x, y) ∈ nladderN (2 * k + 2) ↔ WinN4 k x y := by
  rw [SiteCoversNear.mem_nladderN_iff, mem_nladderF (by omega : (2 : ℤ) ≤ 2 * k + 2)]
  dsimp only
  simp only [WinN4, Apart, Bpart, Cpart, Dpart, Excl]
  exact ⟨fun h => by omega, fun h => by omega⟩

theorem InH_n4_even (k x y : ℤ) (hk : 1 ≤ k) (hp : (x + y) % 2 = 0) :
    InH ⟨2 * k + 1, 2 * k + 3⟩ (x, y) ↔
      (-8 * k ^ 2 - 24 * k - 12 ≤ (2 * k + 1) * x - (2 * k + 3) * y ∧ (2 * k + 1) * x - (2 * k + 3) * y ≤ 4 * k + 2 ∧
        0 ≤ (4 * k + 4) * x + 2 * y ∧ (4 * k + 4) * x + 2 * y ≤ 8 * k ^ 2 + 28 * k + 16) := by
  have hmu : muOf ⟨2 * k + 1, 2 * k + 3⟩ = 1 := by unfold muOf; dsimp only; rw [if_neg (by omega)]
  have ha : aOf ⟨2 * k + 1, 2 * k + 3⟩ true = 2 := by
    unfold aOf; rw [if_pos rfl]; dsimp only; omega
  have hl : lOf ⟨2 * k + 1, 2 * k + 3⟩ true = 0 := by unfold lOf; rw [if_pos rfl]
  have hT : tOf ⟨2 * k + 1, 2 * k + 3⟩ = 8 * k ^ 2 + 24 * k + 14 := by unfold tOf; ring
  unfold InH
  simp only [decide_eq_true hp, ha, hl, hmu, hT, tCo, sCo]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩

theorem InH_n4_odd (k x y : ℤ) (hk : 1 ≤ k) (hp : (x + y) % 2 ≠ 0) :
    InH ⟨2 * k + 1, 2 * k + 3⟩ (x, y) ↔
      (-8 * k ^ 2 - 22 * k - 13 ≤ (2 * k + 1) * x - (2 * k + 3) * y ∧ (2 * k + 1) * x - (2 * k + 3) * y ≤ 2 * k + 3 ∧
        2 ≤ (4 * k + 4) * x + 2 * y ∧ (4 * k + 4) * x + 2 * y ≤ 8 * k ^ 2 + 28 * k + 14) := by
  have hmu : muOf ⟨2 * k + 1, 2 * k + 3⟩ = 1 := by unfold muOf; dsimp only; rw [if_neg (by omega)]
  have ha : aOf ⟨2 * k + 1, 2 * k + 3⟩ false = 2 * k + 1 := by unfold aOf; rw [if_neg (by simp)]
  have hl : lOf ⟨2 * k + 1, 2 * k + 3⟩ false = 2 := by
    unfold lOf
    rw [if_neg (by simp)]
    dsimp only
    omega
  have hT : tOf ⟨2 * k + 1, 2 * k + 3⟩ = 8 * k ^ 2 + 24 * k + 14 := by unfold tOf; ring
  unfold InH
  simp only [decide_eq_false hp, ha, hl, hmu, hT, tCo, sCo]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩

/-- The `D` part on even sites, without the exclusions, gives the four even inequalities once `E` and `F` are excluded. -/
theorem even_fwd4 (k x y : ℤ) (hk : 1 ≤ k) (hp : (x + y) % 2 = 0) (hD : Dpart k x y) (hE : ¬ (x = -1 ∧ y ≤ 2 * k + 2))
    (hF : ¬ (x = 2 * k + 3 ∧ 4 * k + 2 ≤ y)) :
    -8 * k ^ 2 - 24 * k - 12 ≤ (2 * k + 1) * x - (2 * k + 3) * y ∧ (2 * k + 1) * x - (2 * k + 3) * y ≤ 4 * k + 2 ∧
      0 ≤ (4 * k + 4) * x + 2 * y ∧ (4 * k + 4) * x + 2 * y ≤ 8 * k ^ 2 + 28 * k + 16 := by
  obtain ⟨hx1, hx2, hy0, hy1, hd1, hd2⟩ := hD
  have hr1 : 0 ≤ y - x + 2 := by omega
  have hr2 : 0 ≤ 4 * k + 4 - (y - x) := by omega
  have hq2 : 0 ≤ 6 * k + 4 - y := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases le_total x (2 * k) with hxk | hxk
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) hr2]
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 1 by omega) (show (0 : ℤ) ≤ x - 2 * k by omega),
        mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) hq2]
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 1 by omega) hr1]
  · rcases eq_or_lt_of_le hx1 with hx | hx
    · have hxe : x = -1 := hx.symm
      have : 2 * k + 3 ≤ y := by
        by_contra h
        exact hE ⟨hxe, by omega⟩
      subst hxe
      nlinarith
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) (show (0 : ℤ) ≤ x + 1 by omega)]
  · rcases le_or_gt x (2 * k + 2) with hxk | hxk
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) (show (0 : ℤ) ≤ 2 * k + 2 - x by omega)]
    · have hxe : x = 2 * k + 3 := by omega
      have : y ≤ 4 * k + 1 := by
        by_contra h
        exact hF ⟨hxe, by omega⟩
      subst hxe
      nlinarith

/-- The even `H` inequalities give the `D` part with the exclusions, on even sites. -/
theorem even_bwd4 (k x y : ℤ) (hk : 1 ≤ k) (hp : (x + y) % 2 = 0)
    (e1 : -8 * k ^ 2 - 24 * k - 12 ≤ (2 * k + 1) * x - (2 * k + 3) * y)
    (e2 : (2 * k + 1) * x - (2 * k + 3) * y ≤ 4 * k + 2) (e3 : 0 ≤ (4 * k + 4) * x + 2 * y)
    (e4 : (4 * k + 4) * x + 2 * y ≤ 8 * k ^ 2 + 28 * k + 16) :
    Dpart k x y ∧ ¬ (x = -1 ∧ y ≤ 2 * k + 2) ∧ ¬ (x = 2 * k + 3 ∧ 4 * k + 2 ≤ y) := by
  have hy0 : 0 ≤ y := by
    by_contra hc
    have hc' : y ≤ -1 := by omega
    have hx1 : 1 ≤ x := by
      by_contra h
      have h' : x ≤ 0 := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) (show (0 : ℤ) ≤ -x by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ -1 - y by omega),
      mul_nonneg (show (0 : ℤ) ≤ 2 * k + 1 by omega) (show (0 : ℤ) ≤ x - 1 by omega)]
  have hx1' : -1 ≤ x := by
    by_contra hc
    have hc' : x ≤ -2 := by omega
    have hy4 : 4 * k + 4 ≤ y := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) (show (0 : ℤ) ≤ -2 - x by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ y - (4 * k + 4) by omega),
      mul_nonneg (show (0 : ℤ) ≤ 2 * k + 1 by omega) (show (0 : ℤ) ≤ -2 - x by omega)]
  have hx2 : x ≤ 2 * k + 3 := by
    by_contra hc
    have hc' : 2 * k + 4 ≤ x := by omega
    have hy2 : y ≤ 2 * k := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) (show (0 : ℤ) ≤ x - (2 * k + 4) by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ 2 * k - y by omega),
      mul_nonneg (show (0 : ℤ) ≤ 2 * k + 1 by omega) (show (0 : ℤ) ≤ x - (2 * k + 4) by omega)]
  have hy1 : y ≤ 6 * k + 4 := by
    by_contra hc
    have hc' : 6 * k + 5 ≤ y := by omega
    have hx3 : x ≤ 2 * k + 1 := by
      by_contra h
      have h' : 2 * k + 2 ≤ x := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) (show (0 : ℤ) ≤ x - (2 * k + 2) by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 1 by omega) (show (0 : ℤ) ≤ 2 * k + 1 - x by omega),
      mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ y - (6 * k + 5) by omega)]
  have hd1 : -2 ≤ y - x := by
    by_contra hc
    have hc3 : y - x ≤ -3 := by omega
    have hc4 : 4 ≤ x - y := by
      have : x - y ≠ 3 := by
        intro h
        omega
      omega
    have hA : 0 ≤ 4 * k + 2 - ((2 * k + 1) * x - (2 * k + 3) * y) := by linarith
    have hB : 0 ≤ 8 * k ^ 2 + 28 * k + 16 - ((4 * k + 4) * x + 2 * y) := by linarith
    have hC : 0 ≤ x - y - 4 := by omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) hA,
      mul_nonneg (show (0 : ℤ) ≤ 4 * k ^ 2 + 12 * k + 7 by nlinarith) hC]
  have hd2 : y - x ≤ 4 * k + 4 := by
    by_contra hc
    have hpar : 4 * k + 6 ≤ y - x := by omega
    have hxm : x ≤ -3 := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ y - x - (4 * k + 6) by omega)]
    omega
  have hnE : ¬ (x = -1 ∧ y ≤ 2 * k + 2) := by
    rintro ⟨hxe, hy⟩
    subst hxe
    have : 2 * k + 2 ≤ y := by nlinarith
    have : y = 2 * k + 2 := by omega
    subst this
    omega
  have hnF : ¬ (x = 2 * k + 3 ∧ 4 * k + 2 ≤ y) := by
    rintro ⟨hxe, hy⟩
    subst hxe
    have : y ≤ 4 * k + 2 := by nlinarith
    have : y = 4 * k + 2 := by omega
    subst this
    omega
  exact ⟨⟨hx1', hx2, hy0, hy1, hd1, hd2⟩, hnE, hnF⟩

/-- The window on odd sites gives the four odd inequalities. -/
theorem odd_fwd4 (k x y : ℤ) (hk : 1 ≤ k) (hp : (x + y) % 2 ≠ 0) (hW : Apart k x y ∨ Bpart k x y ∨ Cpart k x y ∨ Dpart k x y)
    (hE : ¬ (x = -1 ∧ y ≤ 2 * k + 2)) (hF : ¬ (x = 2 * k + 3 ∧ 4 * k + 2 ≤ y)) :
    -8 * k ^ 2 - 22 * k - 13 ≤ (2 * k + 1) * x - (2 * k + 3) * y ∧ (2 * k + 1) * x - (2 * k + 3) * y ≤ 2 * k + 3 ∧
      2 ≤ (4 * k + 4) * x + 2 * y ∧ (4 * k + 4) * x + 2 * y ≤ 8 * k ^ 2 + 28 * k + 14 := by
  have hsplit : (4 * k + 4) * x + 2 * y = 2 * ((2 * k + 2) * x + y) := by ring
  rcases hW with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hy, hx0, hx1⟩ | ⟨hd1, hd2, hd3, hd4, hd5, hd6⟩
  · subst hx
    subst hy
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · subst hx
    subst hy
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · subst hy
    refine ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩
  · have hr1 : 1 ≤ y - x + 2 := by omega
    have hr2 : 0 ≤ 4 * k + 4 - (y - x) := by omega
    have hq2 : 0 ≤ 6 * k + 4 - y := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases le_or_gt x (2 * k) with hxk | hxk
      · have hr2' : 1 ≤ 4 * k + 4 - (y - x) := by omega
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ 4 * k + 4 - (y - x) - 1 by omega),
          mul_nonneg (show (0 : ℤ) ≤ 2 * k by omega) (show (0 : ℤ) ≤ 2 * k - x by omega)]
      · nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) hq2,
          mul_nonneg (show (0 : ℤ) ≤ 2 * k + 1 by omega) (show (0 : ℤ) ≤ x - 2 * k - 1 by omega)]
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 1 by omega) (show (0 : ℤ) ≤ y - x + 1 by omega)]
    · rcases (show x = -1 ∨ 0 ≤ x by omega) with hxm | hxp
      · subst hxm
        have : 2 * k + 3 ≤ y := by
          by_contra h
          exact hE ⟨rfl, by omega⟩
        nlinarith
      · have hs0 : 0 ≤ (4 * k + 4) * x + 2 * y := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) hxp]
        have hne : (4 * k + 4) * x + 2 * y ≠ 0 := by
          intro h0
          have hx0' : x = 0 := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) hxp]
          subst hx0'
          have hy0' : y = 0 := by omega
          subst hy0'
          omega
        omega
    · have h16 : (4 * k + 4) * x + 2 * y ≤ 8 * k ^ 2 + 28 * k + 16 := by
        rcases le_or_gt x (2 * k + 2) with hxk | hxk
        · nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) (show (0 : ℤ) ≤ 2 * k + 2 - x by omega)]
        · have hxe : x = 2 * k + 3 := by omega
          have : y ≤ 4 * k + 1 := by
            by_contra h
            exact hF ⟨hxe, by omega⟩
          subst hxe
          nlinarith
      have hne16 : (4 * k + 4) * x + 2 * y ≠ 8 * k ^ 2 + 28 * k + 16 := by
        intro h16e
        rcases le_or_gt x (2 * k + 2) with hxk | hxk
        · have h1 : (4 * k + 4) * (2 * k + 2 - x) = 0 := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) (show (0 : ℤ) ≤ 2 * k + 2 - x by omega), mul_nonneg (show (0 : ℤ) ≤ 2 by omega) hq2]
          have h2 : 2 * k + 2 - x = 0 := by
            rcases mul_eq_zero.mp h1 with h | h
            · omega
            · exact h
          have h3 : 6 * k + 4 - y = 0 := by nlinarith
          omega
        · have hxe : x = 2 * k + 3 := by omega
          have : y ≤ 4 * k + 1 := by
            by_contra h
            exact hF ⟨hxe, by omega⟩
          subst hxe
          nlinarith
      omega

/-- The four odd inequalities give the window on odd sites. -/
theorem odd_bwd4 (k x y : ℤ) (hk : 1 ≤ k) (hp : (x + y) % 2 ≠ 0)
    (o1 : -8 * k ^ 2 - 22 * k - 13 ≤ (2 * k + 1) * x - (2 * k + 3) * y)
    (o2 : (2 * k + 1) * x - (2 * k + 3) * y ≤ 2 * k + 3)
    (o3 : 2 ≤ (4 * k + 4) * x + 2 * y) (o4 : (4 * k + 4) * x + 2 * y ≤ 8 * k ^ 2 + 28 * k + 14) :
    WinN4 k x y := by
  have hy0 : 0 ≤ y := by
    by_contra hc
    have hc' : y ≤ -1 := by omega
    have hx1 : 1 ≤ x := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) (show (0 : ℤ) ≤ 1 - 0 by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ -1 - y by omega),
      mul_nonneg (show (0 : ℤ) ≤ 2 * k + 1 by omega) (show (0 : ℤ) ≤ x - 1 by omega)]
  have hx1' : -1 ≤ x := by
    by_contra hc
    have hc' : x ≤ -2 := by omega
    have hy4 : 4 * k + 5 ≤ y := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) (show (0 : ℤ) ≤ -2 - x by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ y - (4 * k + 5) by omega),
      mul_nonneg (show (0 : ℤ) ≤ 2 * k + 1 by omega) (show (0 : ℤ) ≤ -2 - x by omega)]
  have hx2 : x ≤ 2 * k + 3 := by
    by_contra hc
    have hc' : 2 * k + 4 ≤ x := by omega
    have hy2 : y ≤ 2 * k - 1 := by nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) (show (0 : ℤ) ≤ x - (2 * k + 4) by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ 2 * k - 1 - y by omega),
      mul_nonneg (show (0 : ℤ) ≤ 2 * k + 1 by omega) (show (0 : ℤ) ≤ x - (2 * k + 4) by omega)]
  have hy4 : y ≤ 6 * k + 4 := by
    by_contra hc
    have hc' : 6 * k + 5 ≤ y := by omega
    have hx3 : x ≤ 2 * k + 1 := by
      by_contra h
      have h' : 2 * k + 2 ≤ x := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 4 * k + 4 by omega) (show (0 : ℤ) ≤ x - (2 * k + 2) by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 1 by omega) (show (0 : ℤ) ≤ 2 * k + 1 - x by omega),
      mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ y - (6 * k + 5) by omega)]
  by_cases hD1 : -2 ≤ y - x ∧ y - x ≤ 4 * k + 4
  · have hD : Dpart k x y := ⟨hx1', hx2, hy0, hy4, hD1.1, hD1.2⟩
    refine ⟨Or.inr (Or.inr (Or.inr hD)), ?_⟩
    rintro (⟨hxe, hye⟩ | ⟨hxe, hye⟩)
    · subst hxe
      omega
    · subst hxe
      nlinarith
  by_cases hA : 4 * k + 5 ≤ y - x
  · have hxm : x ≤ -1 := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ y - x - (4 * k + 5) by omega)]
    have hxe : x = -1 := by omega
    subst hxe
    have hye : y = 4 * k + 4 := by
      have : y ≤ 4 * k + 4 := by nlinarith
      omega
    subst hye
    refine ⟨Or.inl ⟨rfl, rfl⟩, ?_⟩
    rintro (⟨_, h⟩ | ⟨_, h⟩)
    · omega
    · omega
  have hc3 : x - y ≥ 3 := by omega
  have hc5 : x - y ≤ 3 := by
    by_contra hc
    have hc5' : 5 ≤ x - y := by
      have : x - y ≠ 4 := by
        intro h
        omega
      omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ 2 * k + 3 + 0 by omega),
      mul_nonneg (show (0 : ℤ) ≤ 2 * k + 3 by omega) (show (0 : ℤ) ≤ (2 * k + 1) * (x - y) - 2 * y - (2 * k + 3) by nlinarith),
      mul_nonneg (show (0 : ℤ) ≤ 4 * k ^ 2 + 12 * k + 7 by nlinarith) (show (0 : ℤ) ≤ x - y - 5 by omega)]
  have hc : x - y = 3 := by omega
  have hxe : x = y + 3 := by omega
  subst hxe
  have hy2 : 2 * k ≤ y := by nlinarith
  have hy3 : y ≤ 2 * k := by nlinarith
  have hye : y = 2 * k := by omega
  subst hye
  refine ⟨Or.inr (Or.inl ⟨by ring, rfl⟩), ?_⟩
  rintro (⟨_, h⟩ | ⟨_, h⟩)
  · omega
  · omega

theorem nladder_eq4 (k : ℤ) (hk : 1 ≤ k) :
    ((nladderN (2 * k + 2) : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) = HSet ⟨2 * k + 1, 2 * k + 3⟩ := by
  ext ⟨x, y⟩
  rw [Finset.mem_coe, nladder_window k x y hk]
  show _ ↔ InH ⟨2 * k + 1, 2 * k + 3⟩ (x, y)
  by_cases hp : (x + y) % 2 = 0
  · rw [InH_n4_even k x y hk hp]
    constructor
    · rintro ⟨hW, hnE⟩
      rcases hW with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hy, hx0, hx1⟩ | hD
      · exfalso
        subst hx
        subst hy
        omega
      · exfalso
        subst hx
        subst hy
        omega
      · exfalso
        subst hy
        omega
      · exact even_fwd4 k x y hk hp hD (fun h => hnE (Or.inl h)) (fun h => hnE (Or.inr h))
    · intro h
      obtain ⟨hD, hE, hF⟩ := even_bwd4 k x y hk hp h.1 h.2.1 h.2.2.1 h.2.2.2
      exact ⟨Or.inr (Or.inr (Or.inr hD)), fun h' => h'.elim (fun h'' => hE h'') (fun h'' => hF h'')⟩
  · rw [InH_n4_odd k x y hk hp]
    constructor
    · rintro ⟨hW, hnE⟩
      exact odd_fwd4 k x y hk hp hW (fun h => hnE (Or.inl h)) (fun h => hnE (Or.inr h))
    · intro h
      exact odd_bwd4 k x y hk hp h.1 h.2.1 h.2.2.1 h.2.2.2

end FLatticePaper.Tiles.SiteMaskNear4
