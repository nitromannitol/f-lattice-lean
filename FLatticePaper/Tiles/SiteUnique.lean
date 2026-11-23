import FLatticePaper.Tiles.SiteInduction

/-! Task 53, item 4 (the hull band, pure arithmetic): a site of `H_X` whose `t` and `s` lie in the window of the hull note is the
unique representative of its class.

With `a, l` taken at the parity of the site, `T = tOf X`, `μ = muOf X`, the window is
`L − a − T < t < a`, `2N − l < s < l + μT` (`L = D + N`, `N = 2n`). The periods change `t` by `−T` (the second period `V`) and `s`
by `μT` (the first period `U`), and preserve physical parity, so a second representative in `H` forces `t` or `s` outside the window
(`unique_of_bounds`). This is the set `J` of the hull note. -/

namespace FLatticePaper.Tiles.SiteUnique

open FLatticePaper.Farey FLatticePaper.Tiles.SiteInduction

theorem tOf_nonneg (f : Fraction) (hn : 0 < f.num) (hnd : f.num < f.den) : 0 ≤ tOf f := by
  unfold tOf
  nlinarith

theorem muOf_nonneg (f : Fraction) : 0 ≤ muOf f := by
  unfold muOf
  split_ifs <;> norm_num

theorem two_dvd_muOf_mul (f : Fraction) : 2 ∣ muOf f * (f.num + f.den) := by
  unfold muOf
  split_ifs with h
  · exact dvd_mul_right 2 _
  · have h0 : (f.num + f.den) % 2 = 0 := by omega
    rw [one_mul]
    exact Int.dvd_of_emod_eq_zero h0

/-- **The window criterion.** A site of `H_X` lying in the window of its parity is the only site of `H_X` in its class. -/
theorem unique_of_bounds (f : Fraction) (hn : 0 < f.num) (hnd : f.num < f.den) (z : ℤ × ℤ) (hz : InH f z)
    (h1 : tCo f z < aOf f (decide ((z.1 + z.2) % 2 = 0)))
    (h2 : f.den + f.num - aOf f (decide ((z.1 + z.2) % 2 = 0)) - tOf f < tCo f z)
    (h3 : 2 * f.num - lOf f (decide ((z.1 + z.2) % 2 = 0)) < sCo f z)
    (h4 : sCo f z < lOf f (decide ((z.1 + z.2) % 2 = 0)) + muOf f * tOf f) :
    UniqueIn f z := by
  refine ⟨hz, fun w hw hc => ?_⟩
  obtain ⟨k, l, hk1, hk2⟩ := hc
  have hT := tOf_nonneg f hn hnd
  have hμ := muOf_nonneg f
  have e1 : w.1 - z.1 = k * (muOf f * f.den) + l * (f.num - f.den) := by
    simpa [perU, perV] using hk1
  have e2 : w.2 - z.2 = k * (muOf f * f.num) + l * (f.den + f.num) := by
    simpa [perU, perV] using hk2
  have ht : tCo f w = tCo f z - l * tOf f := by
    unfold tCo tOf
    linear_combination f.num * e1 - f.den * e2
  have hs : sCo f w = sCo f z + k * (muOf f * tOf f) := by
    unfold sCo tOf
    linear_combination (f.den + f.num) * e1 + (f.den - f.num) * e2
  obtain ⟨c, hc⟩ := two_dvd_muOf_mul f
  have hsum : w.1 + w.2 - (z.1 + z.2) = 2 * (c * k + f.num * l) := by
    linear_combination e1 + e2 + k * hc
  have hpar : (w.1 + w.2) % 2 = (z.1 + z.2) % 2 := by
    rw [show w.1 + w.2 = (z.1 + z.2) + 2 * (c * k + f.num * l) by linarith]
    exact Int.add_mul_emod_self_left _ _ _
  have hev : decide ((w.1 + w.2) % 2 = 0) = decide ((z.1 + z.2) % 2 = 0) := by rw [hpar]
  have hw' := hw
  unfold InH at hw'
  rw [hev] at hw'
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw'
  rw [ht] at hw1 hw2
  rw [hs] at hw3 hw4
  rcases lt_trichotomy l 0 with hl | hl | hl
  · exfalso
    have hp : 0 ≤ (-l - 1) * tOf f := mul_nonneg (by omega) hT
    nlinarith
  · subst hl
    rcases lt_trichotomy k 0 with hk | hk | hk
    · exfalso
      have hp : 0 ≤ (-k - 1) * (muOf f * tOf f) := mul_nonneg (by omega) (mul_nonneg hμ hT)
      nlinarith
    · subst hk
      have e1' : w.1 - z.1 = 0 := by simpa using e1
      have e2' : w.2 - z.2 = 0 := by simpa using e2
      exact Prod.ext (by omega) (by omega)
    · exfalso
      have hp : 0 ≤ (k - 1) * (muOf f * tOf f) := mul_nonneg (by omega) (mul_nonneg hμ hT)
      nlinarith
  · exfalso
    have hp : 0 ≤ (l - 1) * tOf f := mul_nonneg (by omega) hT
    nlinarith

end FLatticePaper.Tiles.SiteUnique
