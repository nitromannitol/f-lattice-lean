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

end FLatticePaper.Tiles.SiteRot
