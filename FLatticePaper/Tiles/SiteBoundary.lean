import FLatticePaper.Tiles.SiteBand
import FLatticePaper.Tiles.SiteHullOdd

/-! Task 53, item 4 (the inner boundary, index bound): for a site of `H` with `t > −n` (odd sites) or `t > 0` (even sites) the index
`m = x + y` lies in `[1, μL − 1]`, without the band condition `a ≤ t`.

With `M = m − μL` and `k = x − dμ` one has `t = Lk − dM` (ring identity), and the window `L s ≤ L(μT + N − l)` becomes
`(d − n) M + 2nk ≤ 2n − l`. For `M ≥ 1`: `k ≤ 0` gives `t ≤ −d < −n`, and `k ≥ 1` gives `(d − n) ≤ −l`, impossible for both parities.
These are the `t_hi` boundary sites: an outside neighbour violating the upper `t`-edge forces `t > −n` (odd) and `t > 0` (even). -/

namespace FLatticePaper.Tiles.SiteBoundary

open FLatticePaper.Tiles.SiteBand

theorem tband_hi_m_bounds (n d μ x y t s a l : ℤ) (hn : 0 < n) (hnd : n < d)
    (hμ1 : (d + n) % 2 = 1 → μ = 2) (hμ0 : (d + n) % 2 = 0 → μ = 1)
    (ht : t = n * x - d * y) (hs : s = (d + n) * x + (d - n) * y)
    (hsite : ((x + y) % 2 = 1 → a = n ∧ l = min (d - n) (3 * n - d)) ∧
      ((x + y) % 2 = 0 → a = min (2 * n) (d - n) ∧ l = 0))
    (htl : -n < t) (hte : (x + y) % 2 = 0 → 0 < t) (htL : t ≤ d + n - a) (hsl : l ≤ s)
    (hsu : s ≤ μ * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - l) :
    1 ≤ x + y ∧ x + y ≤ μ * (d + n) - 1 := by
  have hid : (d + n) * s = (d ^ 2 + 2 * d * n - n ^ 2) * (x + y) + 2 * n * t := by
    rw [hs, ht]; ring
  have hL : 0 < d + n := by omega
  have hev : (μ * (d + n)) % 2 = 0 := by
    rcases (show (d + n) % 2 = 0 ∨ (d + n) % 2 = 1 by omega) with h | h
    · rw [hμ0 h]; omega
    · rw [hμ1 h]; omega
  have hk : t + d * ((x + y) - μ * (d + n)) = (d + n) * (x - d * μ) := by
    rw [ht]; ring
  have ha1 : 1 ≤ a := by
    by_cases hp : (x + y) % 2 = 1
    · obtain ⟨h1, -⟩ := hsite.1 hp
      omega
    · obtain ⟨h1, -⟩ := hsite.2 (by omega)
      rw [h1]
      have := hn
      have : 0 < d - n := by omega
      have : 0 < 2 * n := by omega
      omega
  constructor
  · by_contra hlow
    have hm : x + y ≤ 0 := by omega
    rcases (show x + y = 0 ∨ x + y ≤ -1 by omega) with h0 | hneg
    · have hy : y = -x := by omega
      have htx : t = (d + n) * x := by rw [ht, hy]; ring
      have hpos := hte (by omega)
      exact no_mul_strict (d + n) x t hL htx hpos (by omega)
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
    · have hpar : (x + y) % 2 = 0 := by omega
      have hpos := hte hpar
      have hM0 : t = (d + n) * (x - d * μ) := by
        have : (x + y) - μ * (d + n) = 0 := by omega
        rw [this] at hk
        linarith
      exact no_mul_strict (d + n) (x - d * μ) t hL hM0 hpos (by omega)
    · obtain ⟨M, hMdef⟩ : ∃ M : ℤ, M = (x + y) - μ * (d + n) := ⟨_, rfl⟩
      have hM1 : 1 ≤ M := by omega
      have hmy : x + y = μ * (d + n) + M := by omega
      have htk : t = (d + n) * (x - d * μ) - d * M := by
        rw [hMdef]
        linarith
      have hLs := mul_le_mul_of_nonneg_left hsu hL.le
      have star : (d ^ 2 + 2 * d * n - n ^ 2) * M + 2 * n * t ≤ (d + n) * (2 * n - l) := by
        have h := hid
        rw [hmy] at h
        nlinarith
      rcases le_or_gt (x - d * μ) 0 with hk0 | hk1
      · -- `k ≤ 0`: `t ≤ −dM ≤ −d < −n`
        have hLk : (d + n) * (x - d * μ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hL.le hk0
        nlinarith
      · -- `k ≥ 1`: the window forces `(d − n) M ≤ −l`
        have key : (d - n) * M + 2 * n * (x - d * μ) ≤ 2 * n - l := by
          have e : (d + n) * ((d - n) * M + 2 * n * (x - d * μ)) =
              (d ^ 2 + 2 * d * n - n ^ 2) * M + 2 * n * t := by
            rw [htk]
            ring
          have h2 : (d + n) * ((d - n) * M + 2 * n * (x - d * μ)) ≤ (d + n) * (2 * n - l) := by
            rw [e]
            exact star
          exact le_of_mul_le_mul_left h2 hL
        have hk2 : 1 ≤ x - d * μ := by omega
        have hdn : (d - n) * M ≥ d - n := by nlinarith
        have hkn : 2 * n * (x - d * μ) ≥ 2 * n := by nlinarith
        by_cases hp : (x + y) % 2 = 1
        · obtain ⟨-, hl⟩ := hsite.1 hp
          rw [hl] at key
          omega
        · obtain ⟨-, hl⟩ := hsite.2 (by omega)
          rw [hl] at key
          omega

/-- **The `s`-side index of the odd boundary.** For an odd site with `s < L` (and an even site with `s < 2d`) the rotated site
`ψ(x,y) = (−y+n+d, x−n−1+d)` lies in the `t`-window of `X' = (d−n, d+n)` with `t' = L − s`, and `0 ≤ y − x ≤ 2d − 2`. -/
theorem vband_hi_M_odd (n d x y t s a l : ℤ) (hn : 0 < n) (hnd : n < d) (hodd : (d + n) % 2 = 1)
    (ht : t = n * x - d * y) (hs : s = (d + n) * x + (d - n) * y)
    (hsite : ((x + y) % 2 = 1 → a = n ∧ l = min (d - n) (3 * n - d)) ∧
      ((x + y) % 2 = 0 → a = min (2 * n) (d - n) ∧ l = 0))
    (hH1 : a - (d ^ 2 + 2 * d * n - n ^ 2) ≤ t) (hH2 : t ≤ d + n - a) (hH3 : l ≤ s)
    (hsodd : (x + y) % 2 = 1 → s < d + n) (heven : (x + y) % 2 = 0 → s < 2 * d) :
    0 ≤ y - x ∧ y - x ≤ 2 * d - 2 := by
  obtain ⟨x', hx'⟩ : ∃ x' : ℤ, x' = -y + n + d := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : ℤ, y' = x - n - 1 + d := ⟨_, rfl⟩
  have hsum : x' + y' = x - y + 2 * d - 1 := by omega
  have hti : (d + n) - s = (d - n) * x' - (d + n) * y' := by
    rw [hx', hy', hs]; ring
  have hsi : 2 * t + 2 * (d ^ 2 + 2 * d * n - n ^ 2) - 2 * n =
      (d + n + (d - n)) * x' + (d + n - (d - n)) * y' := by
    rw [hx', hy', ht]; ring
  have hT' : (d + n) ^ 2 + 2 * (d + n) * (d - n) - (d - n) ^ 2 = 2 * (d ^ 2 + 2 * d * n - n ^ 2) := by ring
  generalize hTd : d ^ 2 + 2 * d * n - n ^ 2 = T at hH1 hsi hT'
  have hμ1 : (d + n + (d - n)) % 2 = 1 → (1 : ℤ) = 2 := fun h => by omega
  have hμ0 : (d + n + (d - n)) % 2 = 0 → (1 : ℤ) = 1 := fun _ => rfl
  rcases (show (x + y) % 2 = 0 ∨ (x + y) % 2 = 1 by omega) with hz | hz
  · -- even site: `a = min(2n, d − n)`, `l = 0`; the rotated site is odd
    obtain ⟨ha, hl⟩ := hsite.2 hz
    rw [ha] at hH1 hH2
    rw [hl] at hH3
    have hs2d := heven hz
    have hMid := tband_hi_m_bounds (d - n) (d + n) 1 x' y' ((d + n) - s) (2 * t + 2 * T - 2 * n)
      (d - n) (min (d + n - (d - n)) (3 * (d - n) - (d + n))) (by omega) (by omega) hμ1 hμ0 hti hsi
      ⟨fun _ => ⟨rfl, rfl⟩, fun h => by omega⟩
      (by omega) (fun h => by omega) (by omega) (by omega) (by rw [hT']; omega)
    omega
  · -- odd site: `a = n`, `l = min(d − n, 3n − d)`; the rotated site is even
    obtain ⟨ha, hl⟩ := hsite.1 hz
    rw [ha] at hH1 hH2
    rw [hl] at hH3
    have hsL := hsodd hz
    have hMid := tband_hi_m_bounds (d - n) (d + n) 1 x' y' ((d + n) - s) (2 * t + 2 * T - 2 * n)
      (min (2 * (d - n)) (d + n - (d - n))) 0 (by omega) (by omega) hμ1 hμ0 hti hsi
      ⟨fun h => by omega, fun _ => ⟨rfl, rfl⟩⟩
      (by omega) (fun h => by omega) (by omega) (by omega) (by rw [hT']; omega)
    omega

/-- **The `s`-side index of the even boundary.** The even-tile analogue of `vband_hi_M_odd`, rotated by `(p, q)` with
`n = q − p`, `d = q + p`: `ψ(x,y) = (2q − y, x + 2p − 1)`. -/
theorem vband_hi_M_even (n d x y t s a l : ℤ) (hn : 0 < n) (hnd : n < d) (heven : (d + n) % 2 = 0) (hdodd : d % 2 = 1)
    (ht : t = n * x - d * y) (hs : s = (d + n) * x + (d - n) * y)
    (hsite : ((x + y) % 2 = 1 → a = n ∧ l = min (d - n) (3 * n - d)) ∧
      ((x + y) % 2 = 0 → a = min (2 * n) (d - n) ∧ l = 0))
    (hH1 : a - (d ^ 2 + 2 * d * n - n ^ 2) ≤ t) (hH2 : t ≤ d + n - a) (hH3 : l ≤ s)
    (hsodd : (x + y) % 2 = 1 → s < d + n) (hseven : (x + y) % 2 = 0 → s < 2 * d) :
    0 ≤ y - x ∧ y - x ≤ 2 * d - 2 := by
  obtain ⟨p, hp⟩ : ∃ p : ℤ, d - n = 2 * p := ⟨(d - n) / 2, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q : ℤ, d + n = 2 * q := ⟨(d + n) / 2, by omega⟩
  have hnq : n = q - p := by omega
  have hdq : d = q + p := by omega
  obtain ⟨x', hx'⟩ : ∃ x' : ℤ, x' = -y + 2 * q := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : ℤ, y' = x + 2 * p - 1 := ⟨_, rfl⟩
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℤ, s0 = q * x + p * y := ⟨_, rfl⟩
  have hs2 : s = 2 * s0 := by
    rw [hs, hq, hp, hs0]
    ring
  have ht' : q - s0 = p * x' - q * y' := by
    rw [hx', hy', hs0]
    ring
  have hs' : (q + p) * x' + (q - p) * y' = t + 2 * (q ^ 2 + 2 * q * p - p ^ 2) - (q - p) := by
    rw [hx', hy', ht, hnq, hdq]
    ring
  have hT : (q + p) ^ 2 + 2 * (q + p) * (q - p) - (q - p) ^ 2 = 2 * (q ^ 2 + 2 * q * p - p ^ 2) := by ring
  have hTd : d ^ 2 + 2 * d * n - n ^ 2 = 2 * (q ^ 2 + 2 * q * p - p ^ 2) := by
    rw [hdq, hnq]
    ring
  have hp0 : 0 < p := by omega
  have hpq : p < q := by omega
  have hμ0 : (q + p) % 2 = 0 → (2 : ℤ) = 1 := fun h => by omega
  rcases (show (x + y) % 2 = 0 ∨ (x + y) % 2 = 1 by omega) with hz | hz
  · -- even site: `a = min(2n, d − n)`, `l = 0`; the rotated site is odd
    obtain ⟨ha, hl⟩ := hsite.2 hz
    rw [ha] at hH1 hH2
    rw [hl] at hH3
    have hsd := hseven hz
    have hMid := tband_hi_m_bounds p q 2 x' y' (q - s0) ((q + p) * x' + (q - p) * y') p
      (min (q - p) (3 * p - q)) hp0 hpq (fun _ => rfl) hμ0 ht' rfl
      ⟨fun _ => ⟨rfl, rfl⟩, fun h => by omega⟩
      (by omega) (fun h => by omega) (by omega) (by rw [hs']; omega) (by rw [hs']; omega)
    omega
  · -- odd site: `a = n`, `l = min(d − n, 3n − d)`; the rotated site is even
    obtain ⟨ha, hl⟩ := hsite.1 hz
    rw [ha] at hH1 hH2
    rw [hl] at hH3
    have hsL := hsodd hz
    have hMid := tband_hi_m_bounds p q 2 x' y' (q - s0) ((q + p) * x' + (q - p) * y') (min (2 * p) (q - p)) 0
      hp0 hpq (fun _ => rfl) hμ0 ht' rfl
      ⟨fun h => by omega, fun _ => ⟨rfl, rfl⟩⟩
      (by omega) (fun h => by omega) (by omega) (by rw [hs']; omega) (by rw [hs']; omega)
    omega

end FLatticePaper.Tiles.SiteBoundary
