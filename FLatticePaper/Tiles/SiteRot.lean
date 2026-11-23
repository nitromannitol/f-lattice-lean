import FLatticePaper.Tiles.SiteBand

/-! Task 53, item 4 (the vertical band by rotation): the lower vertical band of `H_X` is the horizontal band of the rotated
fraction `X' = (d − n, d + n)` at the rotated site `ψ(x, y) = (−y + n + d, x − n − 1 + d)`.

Under `ψ`: `t'(ψ z) = L − s(z)`, `s'(ψ z) = 2 t(z) + 2T − 2n`, `T' = 2T`, and the parity flips. The window of `H_X` maps into the window
of `H_{X'}`, so `x' + y' = 2d − 1 − (y − x)` lies in `[1, 2d − 1]` by `tband_m_bounds`: `0 ≤ y − x ≤ 2d − 2`. -/

namespace FLatticePaper.Tiles.SiteRot

open FLatticePaper.Tiles.SiteBand

theorem vband_M_bounds (n d x y t s a l : ℤ) (hn : 0 < n) (hnd : n < d) (hodd : (d + n) % 2 = 1)
    (ht : t = n * x - d * y) (hs : s = (d + n) * x + (d - n) * y)
    (hsite : ((x + y) % 2 = 1 → a = n ∧ l = min (d - n) (3 * n - d)) ∧
      ((x + y) % 2 = 0 → a = min (2 * n) (d - n) ∧ l = 0))
    (hH1 : a - (d ^ 2 + 2 * d * n - n ^ 2) ≤ t) (hH2 : t ≤ d + n - a) (hH3 : l ≤ s)
    (hsband : s ≤ 2 * n - l) :
    0 ≤ y - x ∧ y - x ≤ 2 * d - 2 := by
  obtain ⟨x', hx'⟩ : ∃ x' : ℤ, x' = -y + n + d := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y' : ℤ, y' = x - n - 1 + d := ⟨_, rfl⟩
  have hsum : x' + y' = x - y + 2 * d - 1 := by omega
  have hti : (d + n) - s = (d - n) * x' - (d + n) * y' := by
    rw [hx', hy', hs]; ring
  have hsi : 2 * t + 2 * (d ^ 2 + 2 * d * n - n ^ 2) - 2 * n = (d + n + (d - n)) * x' + (d + n - (d - n)) * y' := by
    rw [hx', hy', ht]; ring
  have hT' : (d + n) ^ 2 + 2 * (d + n) * (d - n) - (d - n) ^ 2 = 2 * (d ^ 2 + 2 * d * n - n ^ 2) := by ring
  have hL' : d + n + (d - n) = 2 * d := by ring
  generalize hTd : d ^ 2 + 2 * d * n - n ^ 2 = T at hH1 hsi hT'
  rcases (show (x + y) % 2 = 1 ∨ (x + y) % 2 = 0 by omega) with hz | hz
  · -- the odd site: `a = n`, `l = min(d − n, 3n − d)`; the rotated site is even
    obtain ⟨ha, hl⟩ := hsite.1 hz
    rw [ha] at hH1 hH2
    rw [hl] at hH3 hsband
    have hpar : (x' + y') % 2 = 0 := by omega
    have key := tband_m_bounds (d - n) (d + n) 1 x' y' ((d + n) - s) (2 * t + 2 * T - 2 * n)
      (min (2 * (d - n)) (d + n - (d - n))) 0 (by omega) (by omega) (fun h => by omega) (fun _ => rfl)
      hti hsi
      ⟨fun h => absurd hpar (by omega), fun _ => ⟨rfl, rfl⟩⟩
      (by omega) (by omega) (by omega) (by rw [hT']; omega)
    omega
  · -- the even site: `a = min(2n, d − n)`, `l = 0`; the rotated site is odd
    obtain ⟨ha, hl⟩ := hsite.2 hz
    rw [ha] at hH1 hH2
    rw [hl] at hH3 hsband
    have hpar : (x' + y') % 2 = 1 := by omega
    have key := tband_m_bounds (d - n) (d + n) 1 x' y' ((d + n) - s) (2 * t + 2 * T - 2 * n)
      (d - n) (min (d + n - (d - n)) (3 * (d - n) - (d + n))) (by omega) (by omega) (fun h => by omega) (fun _ => rfl)
      hti hsi
      ⟨fun _ => ⟨rfl, rfl⟩, fun h => absurd hpar (by omega)⟩
      (by omega) (by omega) (by omega) (by rw [hT']; omega)
    omega

/-- **The even vertical index.** For an even site-type fraction `(n, d)` (`n + d` even, `d` odd) the rotated site
`ψ(x,y) = (2q − y, x + 2p − 1)` with `p = (d−n)/2`, `q = (d+n)/2` lies in the horizontal window of `(p, q)`, and `0 ≤ y − x ≤ 2d − 2`
on the lower vertical band. -/
theorem vband_M_even (n d x y t s a l : ℤ) (hn : 0 < n) (hnd : n < d) (heven : (d + n) % 2 = 0) (hdodd : d % 2 = 1)
    (ht : t = n * x - d * y) (hs : s = (d + n) * x + (d - n) * y)
    (hsite : ((x + y) % 2 = 1 → a = n ∧ l = min (d - n) (3 * n - d)) ∧
      ((x + y) % 2 = 0 → a = min (2 * n) (d - n) ∧ l = 0))
    (hH1 : a - (d ^ 2 + 2 * d * n - n ^ 2) ≤ t) (hH2 : t ≤ d + n - a) (hH3 : l ≤ s)
    (hsband : s ≤ 2 * n - l) :
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
    rw [hl] at hH3 hsband
    have hMid := tband_m_bounds p q 2 x' y' (q - s0) ((q + p) * x' + (q - p) * y') p
      (min (q - p) (3 * p - q)) hp0 hpq (fun _ => rfl) (fun h => by omega) ht' rfl
      ⟨fun _ => ⟨rfl, rfl⟩, fun h => by omega⟩
      (by omega) (by omega) (by rw [hs']; omega) (by rw [hs']; omega)
    omega
  · -- odd site: `a = n`, `l = min(d − n, 3n − d)`; the rotated site is even
    obtain ⟨ha, hl⟩ := hsite.1 hz
    rw [ha] at hH1 hH2
    rw [hl] at hH3 hsband
    have hMid := tband_m_bounds p q 2 x' y' (q - s0) ((q + p) * x' + (q - p) * y') (min (2 * p) (q - p)) 0
      hp0 hpq (fun _ => rfl) (fun h => by omega) ht' rfl
      ⟨fun h => by omega, fun _ => ⟨rfl, rfl⟩⟩
      (by omega) (by omega) (by rw [hs']; omega) (by rw [hs']; omega)
    omega

end FLatticePaper.Tiles.SiteRot
