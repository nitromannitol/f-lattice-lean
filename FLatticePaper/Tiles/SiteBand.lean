import FLatticePaper.Tiles.SiteUnique

/-! Task 53, item 4 (the horizontal band, arithmetic): the index `m = x + y` of a site of `H` in the `t`-band lies in `[1, μL − 1]`.

With `L = d + n`, `N = 2n`, `C = d − n`, `T = d² + 2dn − n²`, and the identities `t = n x − d y`, `s = L x + C y`, `L s = T (x + y) + N t`:
* `m = 0` forces `t = L x`, impossible for `0 < t < L`;
* `m ≤ −1` (odd site) or `m ≤ −2` (even site) forces `s < l`, impossible by the window;
* `m = μL` forces `t = L(x − d μ)`, impossible; `m ≥ μL + 1` (odd site) or `m ≥ μL + 2` (even site) forces `s > μT + N − l`.
The hypotheses are the window of `H` and the parity split; the arithmetic is linear in the products `T·m`, `L·s`, `N·t`. -/

namespace FLatticePaper.Tiles.SiteBand

theorem T_nonneg (n d : ℤ) (hn : 0 < n) (hnd : n < d) : 0 ≤ d ^ 2 + 2 * d * n - n ^ 2 := by
  nlinarith

/-- The odd-site lower bound: `x + y ≤ −1` contradicts the window `l ≤ s`. -/
theorem odd_low (n d x y t s : ℤ) (hn : 0 < n) (hnd : n < d)
    (hid : (d + n) * s = (d ^ 2 + 2 * d * n - n ^ 2) * (x + y) + 2 * n * t) (htb : t ≤ d) (hsl : min (d - n) (3 * n - d) ≤ s) (hm : x + y ≤ -1) : False := by
  have hT := T_nonneg n d hn hnd
  have hTm : (d ^ 2 + 2 * d * n - n ^ 2) * (x + y) ≤ -(d ^ 2 + 2 * d * n - n ^ 2) := by
    nlinarith
  have hN : 2 * n * t ≤ 2 * n * d := by
    apply mul_le_mul_of_nonneg_left htb
    omega
  rcases le_total (d - n) (3 * n - d) with h | h
  · rw [min_eq_left h] at hsl
    nlinarith
  · rw [min_eq_right h] at hsl
    nlinarith

/-- The even-site lower bound: `x + y ≤ −2` (even) contradicts `0 ≤ s`. -/
theorem even_low (n d x y t s : ℤ) (hn : 0 < n) (hnd : n < d)
    (hid : (d + n) * s = (d ^ 2 + 2 * d * n - n ^ 2) * (x + y) + 2 * n * t)
    (htb : t ≤ d + n - min (2 * n) (d - n)) (hsl : 0 ≤ s) (hm : x + y ≤ -2) : False := by
  have hT := T_nonneg n d hn hnd
  have hTm : 2 * (d ^ 2 + 2 * d * n - n ^ 2) ≤ -((d ^ 2 + 2 * d * n - n ^ 2) * (x + y)) := by
    nlinarith
  have hN : 2 * n * t ≤ 2 * n * (d + n - min (2 * n) (d - n)) := mul_le_mul_of_nonneg_left htb (by omega)
  have hs0 : 0 ≤ (d + n) * s := mul_nonneg (by omega) hsl
  rcases le_total (2 * n) (d - n) with h | h
  · rw [min_eq_left h] at hN
    nlinarith
  · rw [min_eq_right h] at hN
    nlinarith

/-- A multiple of `L` strictly between `0` and `L` does not exist. -/
theorem no_mul_strict (L k t : ℤ) (hL : 0 < L) (ht : t = L * k) (h1 : 0 < t) (h2 : t < L) : False := by
  rcases le_or_gt k 0 with hk | hk
  · nlinarith
  · nlinarith

/-- The odd site upper bound: `M = x + y − μL ≥ 1` contradicts `s ≤ μT + N − l`, with `t ≥ n`. -/
theorem odd_high (n d μ x y t s : ℤ) (hn : 0 < n) (hnd : n < d)
    (hid : (d + n) * s = (d ^ 2 + 2 * d * n - n ^ 2) * (x + y) + 2 * n * t)
    (hsu : s ≤ μ * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - min (d - n) (3 * n - d))
    (htn : n ≤ t) (hM : μ * (d + n) + 1 ≤ x + y) : False := by
  have hT := T_nonneg n d hn hnd
  have hLs : (d + n) * s ≤ (d + n) * (μ * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - min (d - n) (3 * n - d)) :=
    mul_le_mul_of_nonneg_left hsu (by omega)
  have hTM : (d ^ 2 + 2 * d * n - n ^ 2) ≤ (d ^ 2 + 2 * d * n - n ^ 2) * (x + y - μ * (d + n)) :=
    le_mul_of_one_le_right hT (by omega)
  have hnt : 2 * n * n ≤ 2 * n * t := mul_le_mul_of_nonneg_left htn (by omega)
  rcases le_total (d - n) (3 * n - d) with h | h
  · rw [min_eq_left h] at hLs
    nlinarith
  · rw [min_eq_right h] at hLs
    nlinarith

/-- The even site upper bound: `M = x + y − μL ≥ 2` contradicts `s ≤ μT + N`, with `t ≥ a`. -/
theorem even_high (n d μ x y t s : ℤ) (hn : 0 < n) (hnd : n < d)
    (hid : (d + n) * s = (d ^ 2 + 2 * d * n - n ^ 2) * (x + y) + 2 * n * t)
    (hsu : s ≤ μ * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n)
    (hta : min (2 * n) (d - n) ≤ t) (hM : μ * (d + n) + 2 ≤ x + y) : False := by
  have hT := T_nonneg n d hn hnd
  have hLs : (d + n) * s ≤ (d + n) * (μ * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n) :=
    mul_le_mul_of_nonneg_left hsu (by omega)
  have hTM : 2 * (d ^ 2 + 2 * d * n - n ^ 2) ≤ (d ^ 2 + 2 * d * n - n ^ 2) * (x + y - μ * (d + n)) :=
    by nlinarith
  have hNt : 2 * n * min (2 * n) (d - n) ≤ 2 * n * t := mul_le_mul_of_nonneg_left hta (by omega)
  rcases le_total (2 * n) (d - n) with h | h
  · rw [min_eq_left h] at hNt
    nlinarith
  · rw [min_eq_right h] at hNt
    nlinarith

/-- **The index of a site of the horizontal band.** For a site `z = (x, y)` of `H` whose `t` is in the band `a ≤ t`,
the index `x + y` lies in `[1, μL − 1]`. -/
theorem tband_m_bounds (n d μ x y t s a l : ℤ) (hn : 0 < n) (hnd : n < d)
    (hμ1 : (d + n) % 2 = 1 → μ = 2) (hμ0 : (d + n) % 2 = 0 → μ = 1)
    (ht : t = n * x - d * y) (hs : s = (d + n) * x + (d - n) * y)
    (hsite : ((x + y) % 2 = 1 → a = n ∧ l = min (d - n) (3 * n - d)) ∧
      ((x + y) % 2 = 0 → a = min (2 * n) (d - n) ∧ l = 0))
    (hta : a ≤ t) (htL : t ≤ d + n - a) (hsl : l ≤ s)
    (hsu : s ≤ μ * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - l) :
    1 ≤ x + y ∧ x + y ≤ μ * (d + n) - 1 := by
  have hid : (d + n) * s = (d ^ 2 + 2 * d * n - n ^ 2) * (x + y) + 2 * n * t := by
    rw [hs, ht]; ring
  have hL : 0 < d + n := by omega
  have hev : (μ * (d + n)) % 2 = 0 := by
    rcases (show (d + n) % 2 = 0 ∨ (d + n) % 2 = 1 by omega) with h | h
    · rw [hμ0 h]; omega
    · rw [hμ1 h]; omega
  have ha1 : 1 ≤ a := by
    by_cases hp : (x + y) % 2 = 1
    · obtain ⟨h1, -⟩ := hsite.1 hp
      omega
    · obtain ⟨h1, -⟩ := hsite.2 (by omega)
      rw [h1]
      omega
  constructor
  · by_contra hlow
    have hm : x + y ≤ 0 := by omega
    rcases (show x + y = 0 ∨ x + y ≤ -1 by omega) with h0 | hneg
    · have hy : y = -x := by omega
      have htx : t = (d + n) * x := by rw [ht, hy]; ring
      exact no_mul_strict (d + n) x t hL htx (by omega) (by omega)
    · by_cases hp : (x + y) % 2 = 1
      · obtain ⟨ha, hl⟩ := hsite.1 hp
        rw [ha] at htL
        rw [hl] at hsl
        exact odd_low n d x y t s hn hnd hid (by omega) hsl hneg
      · obtain ⟨ha, hl⟩ := hsite.2 (by omega)
        rw [ha] at htL
        rw [hl] at hsl
        exact even_low n d x y t s hn hnd hid htL hsl (by omega)
  · by_contra hhigh
    have hm : μ * (d + n) ≤ x + y := by omega
    rcases (show x + y = μ * (d + n) ∨ μ * (d + n) + 1 ≤ x + y by omega) with heq | hgt
    · have hy : y = μ * (d + n) - x := by omega
      have htx : t = (d + n) * (x - d * μ) := by rw [ht, hy]; ring
      exact no_mul_strict (d + n) (x - d * μ) t hL htx (by omega) (by omega)
    · by_cases hp : (x + y) % 2 = 1
      · obtain ⟨ha, hl⟩ := hsite.1 hp
        rw [ha] at hta
        rw [hl] at hsu
        exact odd_high n d μ x y t s hn hnd hid hsu hta hgt
      · obtain ⟨ha, hl⟩ := hsite.2 (by omega)
        rw [ha] at hta
        rw [hl] at hsu
        have hsu' : s ≤ μ * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n := by simpa using hsu
        exact even_high n d μ x y t s hn hnd hid hsu' hta (by omega)

end FLatticePaper.Tiles.SiteBand
