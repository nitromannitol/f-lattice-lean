import FLatticePaper.Tiles.PairOwnerP0
import FLatticePaper.Tiles.PairQAbox

/-! Task 53, item 2 (covering reduction), section 10: the flag-false odd child (`δ = dr − ne = +1`, W0), the `P` box.

The cell of `X = P + Q` is the same as at W0, with `U = (2(d+e), 2(n+r))`, `V = (n+r−(d+e), d+e+n+r)`. On the box `[0, α] × [β, 1]`
(`α = d/D`, `β = e/D`, `D = d + e`) the source `P@V_Q` is `HSet P` at `z − V_Q`, `V_Q = (r−e, r+e)`. With `T = T_P`, `K = s_P(Q)`,
`κ = (d−n)/D` (so `α(T+K) = T + κ`, `β(T+K) = K − κ`) the windows are
`t(z − V_Q) = (n+d)/2 + K − 2u − (T+K) v` and `s(z − V_Q) = n − 2 + 2(T+K) u + 2v`.
The facets hold for all proper W0 pairs except `(e, r) = (3, 1)`, `d = 3n + 1`, `n ≥ 3`, at the even lower `t` facet, where
the integrality `2 T_X v ∈ 2ℤ + 1` gives `v ≤ 1 − 1/(2 T_X)`. -/

namespace FLatticePaper.Tiles.PairW0P

open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.PairQAbox

/-- `K = s_P(Q) = (d+n)e + (d−n)r`. -/
def KP (d n e r : ℤ) : ℚ := ((d : ℚ) + n) * e + ((d : ℚ) - n) * r

/-- `T = T_P = d² + 2dn − n²`. -/
def TP (d n : ℤ) : ℚ := (d : ℚ) ^ 2 + 2 * d * n - (n : ℚ) ^ 2

/-- The `t_P` of `z − V_Q` (W0). -/
theorem t_PVQ (d n e r : ℤ) (hdet : d * r - n * e = 1) (z : ℤ × ℤ) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r))) :
    (n : ℚ) * ((z.1 : ℚ) - (r - e)) - (d : ℚ) * ((z.2 : ℚ) - (r + e)) =
      ((d : ℚ) + n) / 2 + KP d n e r - 2 * u - (KP d n e r + TP d n) * v := by
  have hdetQ : (d : ℚ) * r - n * e = 1 := by exact_mod_cast hdet
  unfold KP TP
  linear_combination (n : ℚ) * hz1 - (d : ℚ) * hz2 - 2 * u * hdetQ

/-- The `s_P` of `z − V_Q` (W0). -/
theorem s_PVQ (d n e r : ℤ) (hdet : d * r - n * e = 1) (z : ℤ × ℤ) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r))) :
    ((d : ℚ) + n) * ((z.1 : ℚ) - (r - e)) + ((d : ℚ) - n) * ((z.2 : ℚ) - (r + e)) =
      n - 2 + 2 * (KP d n e r + TP d n) * u + 2 * v := by
  have hdetQ : (d : ℚ) * r - n * e = 1 := by exact_mod_cast hdet
  unfold KP TP
  linear_combination ((d : ℚ) + n) * hz1 + ((d : ℚ) - n) * hz2 + (2 * v - 2) * hdetQ

/-- The box variables and identities for the P window (W0). -/
theorem ab_PW0 (d n e r : ℤ) (hdet : d * r - n * e = 1) (α β κ : ℚ) (hD : (d : ℚ) + e ≠ 0)
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (d : ℚ) - n) :
    α + β = 1 ∧ α * (TP d n + KP d n e r) = TP d n + κ ∧ β * (TP d n + KP d n e r) = KP d n e r - κ := by
  have hdetQ : (d : ℚ) * r - n * e = 1 := by exact_mod_cast hdet
  have h1 : α + β = 1 := by
    have : (α + β) * ((d : ℚ) + e) = 1 * ((d : ℚ) + e) := by linear_combination hα + hβ
    exact mul_right_cancel₀ hD this
  have h2 : (α * (TP d n + KP d n e r)) * ((d : ℚ) + e) = (TP d n + κ) * ((d : ℚ) + e) := by
    unfold KP TP
    linear_combination (((d : ℚ) ^ 2 + 2 * d * n - (n : ℚ) ^ 2) + (((d : ℚ) + n) * e + ((d : ℚ) - n) * r)) * hα
      + ((d : ℚ) - n) * hdetQ - hκ
  have hA : α * (TP d n + KP d n e r) = TP d n + κ := mul_right_cancel₀ hD h2
  refine ⟨h1, hA, ?_⟩
  linear_combination (TP d n + KP d n e r) * h1 - hA

/-- The real facets of the `P@V_Q` box `[0, α] × [β, 1]`: the four window bounds of `t` and `s` (W0). -/
theorem pvq_real (H N KP' TP' α β κ u v : ℚ) (hW : 0 ≤ KP' + TP')
    (hA : α * (TP' + KP') = TP' + κ) (hB : β * (TP' + KP') = KP' - κ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ α) (hv0 : β ≤ v) (hv1 : v ≤ 1) :
    H + KP' - 2 * u - (KP' + TP') * v ≤ H + κ ∧
    H - 2 * α - TP' ≤ H + KP' - 2 * u - (KP' + TP') * v ∧
    N - 2 + 2 * β ≤ N - 2 + 2 * (KP' + TP') * u + 2 * v ∧
    N - 2 + 2 * (KP' + TP') * u + 2 * v ≤ N + 2 * TP' + 2 * κ := by
  have hWv : (KP' + TP') * β ≤ (KP' + TP') * v := mul_le_mul_of_nonneg_left hv0 hW
  have hWv1 : (KP' + TP') * v ≤ (KP' + TP') * 1 := mul_le_mul_of_nonneg_left hv1 hW
  have hWu0 : 0 ≤ (KP' + TP') * u := mul_nonneg hW hu0
  have hWu1 : (KP' + TP') * u ≤ (KP' + TP') * α := mul_le_mul_of_nonneg_left hu1 hW
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The window of `P` as an `InH` statement at a point of fixed parity. -/
theorem inH_P_iff (d n : ℤ) (w : ℤ × ℤ) (ev : Bool) (hev : decide ((w.1 + w.2) % 2 = 0) = ev)
    (hmu : muOf ⟨n, d⟩ = 2) :
    InH ⟨n, d⟩ w ↔
      (aOf ⟨n, d⟩ ev - (d ^ 2 + 2 * d * n - n ^ 2) ≤ n * w.1 - d * w.2 ∧
        n * w.1 - d * w.2 ≤ d + n - aOf ⟨n, d⟩ ev ∧
        lOf ⟨n, d⟩ ev ≤ (d + n) * w.1 + (d - n) * w.2 ∧
        (d + n) * w.1 + (d - n) * w.2 ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - lOf ⟨n, d⟩ ev) := by
  unfold InH
  rw [hev, hmu]
  exact Iff.rfl

/-- `c = d − n = 1` gives `d < e` (W0). -/
theorem c1_lt (d n e r : ℤ) (hn : 0 < n) (hr : 0 < r) (hre : r < e) (hdet : d * r - n * e = 1)
    (heven : (e + r) % 2 = 0) (hc : d - n = 1) : d < e := by
  have key : n * (e - r) = r - 1 := by
    have hd' : d = n + 1 := by omega
    subst hd'
    linarith [hdet]
  by_contra hcon
  push Not at hcon
  have he2 : 2 ≤ e - r := by omega
  have h1 : n * 2 ≤ n * (e - r) := mul_le_mul_of_nonneg_left he2 hn.le
  have hrn : r ≤ n := by omega
  linarith

/-- For `d = 3n ± 1` (and `(e, r) ≠ (3, 1)`) one has `d < 3e` (W0). -/
theorem d3e (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hnot : ¬ (e = 3 ∧ r = 1)) (h : d = 3 * n + 1 ∨ d = 3 * n - 1) : d < 3 * e := by
  rcases h with h | h
  · have key : n * (e - 3 * r) = r - 1 := by
      subst h
      linarith [hdet]
    rcases (show r = 1 ∨ 2 ≤ r by omega) with h1 | h1
    · subst h1
      have h0 : n * (e - 3) = 0 := by linarith [key]
      have he3 : e = 3 := by
        rcases mul_eq_zero.mp h0 with h0 | h0
        · omega
        · omega
      exact absurd ⟨he3, rfl⟩ hnot
    · have hpos : 0 < e - 3 * r := by
        by_contra hc
        push Not at hc
        have : n * (e - 3 * r) ≤ n * 0 := mul_le_mul_of_nonneg_left hc hn.le
        linarith
      have h2 : n ≤ r - 1 := by
        have : n * 1 ≤ n * (e - 3 * r) := mul_le_mul_of_nonneg_left (by omega) hn.le
        linarith
      omega
  · have key : n * (3 * r - e) = r + 1 := by
      subst h
      linarith [hdet]
    by_contra hc
    push Not at hc
    have he : e ≤ n - 1 := by omega
    rcases (show 3 * r - e ≥ 1 ∨ 3 * r - e ≤ 0 by omega) with h3 | h3
    · have : n * 1 ≤ n * (3 * r - e) := mul_le_mul_of_nonneg_left h3 hn.le
      linarith
    · have : n * (3 * r - e) ≤ n * 0 := mul_le_mul_of_nonneg_left h3 hn.le
      linarith

/-- The case split of the odd `s`-lower bound: `min(c, 3n − d) ≤ n − 1`, or `d = 2`, `n = 1`, `d < e`. -/
theorem L_cases (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hre : r < e) (hdet : d * r - n * e = 1) :
    min (d - n) (3 * n - d) ≤ n - 1 ∨ (d = 2 * n ∧ n = 1 ∧ d < e) := by
  by_cases h : min (d - n) (3 * n - d) ≤ n - 1
  · exact Or.inl h
  · right
    have hd2 : d = 2 * n := by omega
    have hkey : n * (2 * r - e) = 1 := by
      subst hd2
      linarith [hdet]
    have hn1 : n = 1 := by
      by_contra hne
      rcases (show 2 * r - e ≥ 1 ∨ 2 * r - e ≤ 0 by omega) with h3 | h3
      · have : n * 1 ≤ n * (2 * r - e) := mul_le_mul_of_nonneg_left h3 hn.le
        have h2 : 2 ≤ n := by omega
        nlinarith
      · have : n * (2 * r - e) ≤ n * 0 := mul_le_mul_of_nonneg_left h3 hn.le
        linarith
    have hk : 2 * r - e = 1 := by
      rw [hn1] at hkey
      linarith
    exact ⟨hd2, hn1, by omega⟩

/-- The odd `t`-lower facet: `2α < (d−n)/2 + 1`. -/
theorem odd_alpha (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (heven : (e + r) % 2 = 0) (hodd : (d + n) % 2 = 1) (α : ℚ)
    (hα : α * ((d : ℚ) + e) = d) : 2 * α < ((d : ℚ) - n) / 2 + 1 := by
  have hDq : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have hdq : (d : ℚ) < e + d := by
    have : (0 : ℤ) < e := by omega
    have : (0 : ℚ) < e := by exact_mod_cast this
    linarith
  by_cases hc : d - n = 1
  · have hlt := c1_lt d n e r hn hr hre hdet heven hc
    have hcq : ((d : ℚ) - n) = 1 := by exact_mod_cast hc
    rw [hcq]
    have hlt' : (d : ℚ) < e := by exact_mod_cast hlt
    nlinarith
  · have hc3 : d - n ≥ 3 := by omega
    have hc3q : ((d : ℚ) - n) ≥ 3 := by exact_mod_cast hc3
    have hα1 : α < 1 := by nlinarith
    linarith

/-- The even `t`-lower facet: `2α < (n+d)/2 − m + 1` for `m = min(2n, d − n)`, with `(e, r) ≠ (3, 1)`. -/
theorem even_alpha (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hnot : ¬ (e = 3 ∧ r = 1)) (hodd : (d + n) % 2 = 1) (α : ℚ)
    (hα : α * ((d : ℚ) + e) = d) (m : ℤ) (hm : m = min (2 * n) (d - n)) :
    2 * α < ((n : ℚ) + d) / 2 - m + 1 := by
  have hDq : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have hα1 : α < 1 := by
    have : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℤ) < e by omega)
    nlinarith
  rcases (show d ≥ 3 * n + 2 ∨ d ≤ 3 * n - 2 ∨ d = 3 * n + 1 ∨ d = 3 * n - 1 by omega) with h | h | h | h
  · have hm2 : m = 2 * n := by omega
    have : ((m : ℤ) : ℚ) = 2 * n := by rw [hm2]; push_cast; ring
    rw [this]
    have : (d : ℚ) ≥ 3 * n + 2 := by exact_mod_cast h
    linarith
  · have hm2 : m = d - n := by omega
    have : ((m : ℤ) : ℚ) = (d : ℚ) - n := by rw [hm2]; push_cast; ring
    rw [this]
    have : (d : ℚ) ≤ 3 * n - 2 := by exact_mod_cast h
    linarith
  · have hm2 : m = 2 * n := by omega
    have : ((m : ℤ) : ℚ) = 2 * n := by rw [hm2]; push_cast; ring
    rw [this]
    have hlt := d3e d n e r hn hnd hr hre hdet hnot (Or.inl h)
    have hlt' : (d : ℚ) < 3 * e := by exact_mod_cast hlt
    have hdq : (d : ℚ) = 3 * n + 1 := by exact_mod_cast h
    nlinarith
  · have hm2 : m = 2 * n - 1 := by omega
    have : ((m : ℤ) : ℚ) = 2 * n - 1 := by rw [hm2]; push_cast; ring
    rw [this]
    have hlt := d3e d n e r hn hnd hr hre hdet hnot (Or.inr h)
    have hlt' : (d : ℚ) < 3 * e := by exact_mod_cast hlt
    have hdq : (d : ℚ) = 3 * n - 1 := by exact_mod_cast h
    nlinarith

/-- The basic positivity facts of the W0 box variables. -/
theorem box_pos_W0 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (_hdet : d * r - n * e = 1) (α β κ : ℚ)
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (d : ℚ) - n) :
    0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧ 0 ≤ κ ∧ κ < 1 ∧ 0 ≤ KP d n e r + TP d n := by
  have hDi : (0 : ℤ) < d + e := by omega
  have hDq : (0 : ℚ) < (d : ℚ) + e := by exact_mod_cast hDi
  have hdq : (0 : ℚ) < d := by exact_mod_cast (show (0 : ℤ) < d by omega)
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  have heq : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℤ) < e by omega)
  have hndq : (n : ℚ) < d := by exact_mod_cast hnd
  have hreq : (r : ℚ) < e := by exact_mod_cast hre
  have hαpos : 0 < α := by
    by_contra h; push Not at h; nlinarith
  have hβpos : 0 < β := by
    by_contra h; push Not at h; nlinarith
  have hκpos : 0 ≤ κ := by
    by_contra h; push Not at h; nlinarith
  have hκlt : κ < 1 := by
    by_contra h; push Not at h; nlinarith
  have hαβ : α + β = 1 := by
    have : (α + β) * ((d : ℚ) + e) = 1 * ((d : ℚ) + e) := by linear_combination hα + hβ
    exact mul_right_cancel₀ (ne_of_gt hDq) this
  refine ⟨hαpos, by linarith, hβpos, by linarith, hκpos, hκlt, ?_⟩
  unfold KP TP
  nlinarith

/-- Odd sites: the integer point `z − V_Q` lies in `HSet P` on the box `[0, α] × [β, 1]` (W0). -/
theorem inH_PVQ_odd (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (d : ℚ) - n)
    (hu0 : 0 ≤ u) (hu1 : u ≤ α) (hv0 : β ≤ v) (hv1 : v ≤ 1) (hpar : (z.1 + z.2) % 2 = 1) :
    InH ⟨n, d⟩ (z.1 - (r - e), z.2 - (r + e)) := by
  obtain ⟨hα0, hα1, hβ0, hβ1, hκ0, hκ1, hW⟩ := box_pos_W0 d n e r hn hnd hr hre hdet α β κ hα hβ hκ
  have hDne : (d : ℚ) + e ≠ 0 := by
    have : (0 : ℤ) < d + e := by omega
    exact ne_of_gt (by exact_mod_cast this)
  obtain ⟨hαβ, hA, hB⟩ := ab_PW0 d n e r hdet α β κ hDne hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := pvq_real (((d : ℚ) + n) / 2) (n : ℚ) (KP d n e r) (TP d n) α β κ u v hW hA hB hu0 hu1 hv0 hv1
  have ht := t_PVQ d n e r hdet z u v hz1 hz2
  have hs := s_PVQ d n e r hdet z u v hz1 hz2
  have hoa := odd_alpha d n e r hn hnd hr hre hdet heven hodd α hα
  unfold KP TP at R1 R2 R3 R4 ht hs
  have hnq : (n : ℚ) < d := by exact_mod_cast hnd
  have hnq0 : (0 : ℚ) < n := by exact_mod_cast hn
  have hLcases := L_cases d n e r hn hnd hre hdet
  have hTlo : n - (d ^ 2 + 2 * d * n - n ^ 2) - 1 < n * (z.1 - (r - e)) - d * (z.2 - (r + e)) := by
    have h : ((n - (d ^ 2 + 2 * d * n - n ^ 2) - 1 : ℤ) : ℚ) < ((n * (z.1 - (r - e)) - d * (z.2 - (r + e)) : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith only [R2, hoa]
    exact_mod_cast h
  have hThi : n * (z.1 - (r - e)) - d * (z.2 - (r + e)) < d + 1 := by
    have h : ((n * (z.1 - (r - e)) - d * (z.2 - (r + e)) : ℤ) : ℚ) < ((d + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith only [R1, hκ1, hnq]
    exact_mod_cast h
  have hDpos : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have hSlo : min (d - n) (3 * n - d) - 1 < (d + n) * (z.1 - (r - e)) + (d - n) * (z.2 - (r + e)) := by
    rcases hLcases with hL' | ⟨hd2, hn1, hde⟩
    · have hmq : ((min (d - n) (3 * n - d) : ℤ) : ℚ) ≤ (n : ℚ) - 1 := by exact_mod_cast hL'
      have key : ((min (d - n) (3 * n - d) : ℤ) : ℚ) - 1 <
          ((d : ℚ) + n) * ((z.1 : ℚ) - ((r : ℚ) - e)) + ((d : ℚ) - n) * ((z.2 : ℚ) - ((r : ℚ) + e)) := by
        linarith only [hs, R3, hmq, hβ0]
      exact_mod_cast key
    · have hmin : min (d - n) (3 * n - d) = 1 := by omega
      rw [hmin]
      have hde' : (d : ℚ) < e := by exact_mod_cast hde
      have hn1' : (n : ℚ) = 1 := by exact_mod_cast (show n = 1 by omega)
      have hprod : 0 < (2 * β - 1) * ((d : ℚ) + e) := by linarith only [hβ, hde']
      have hβhalf : (1 : ℚ) < 2 * β := by nlinarith only [hprod, hDpos]
      have key : (0 : ℚ) <
          ((d : ℚ) + n) * ((z.1 : ℚ) - ((r : ℚ) - e)) + ((d : ℚ) - n) * ((z.2 : ℚ) - ((r : ℚ) + e)) := by
        linarith only [hs, R3, hn1', hβhalf]
      have key' : (0 : ℤ) < (d + n) * (z.1 - (r - e)) + (d - n) * (z.2 - (r + e)) := by exact_mod_cast key
      linarith only [key']
  have hShi : (d + n) * (z.1 - (r - e)) + (d - n) * (z.2 - (r + e)) < 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - min (d - n) (3 * n - d) + 1 := by
    rcases hLcases with hL' | ⟨hd2, hn1, hde⟩
    · have hmq : ((min (d - n) (3 * n - d) : ℤ) : ℚ) ≤ (n : ℚ) - 1 := by exact_mod_cast hL'
      have key : ((d : ℚ) + n) * ((z.1 : ℚ) - ((r : ℚ) - e)) + ((d : ℚ) - n) * ((z.2 : ℚ) - ((r : ℚ) + e)) <
          2 * ((d : ℚ) ^ 2 + 2 * d * n - (n : ℚ) ^ 2) + 2 * n - ((min (d - n) (3 * n - d) : ℤ) : ℚ) + 1 := by
        linarith only [hs, R4, hmq, hκ0, hκ1]
      exact_mod_cast key
    · have hmin : min (d - n) (3 * n - d) = 1 := by omega
      rw [hmin]
      have hn1' : (n : ℚ) = 1 := by exact_mod_cast (show n = 1 by omega)
      have hd2' : (d : ℚ) = 2 := by exact_mod_cast (show d = 2 by omega)
      have hκD : κ * ((d : ℚ) + e) = 1 := by rw [hκ, hd2', hn1']; norm_num
      have hκ2 : κ < 1 / 2 := by
        have he0 : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℤ) < e by omega)
        nlinarith only [hκD, hd2', hDpos, he0, hκ0]
      have key : ((d : ℚ) + n) * ((z.1 : ℚ) - ((r : ℚ) - e)) + ((d : ℚ) - n) * ((z.2 : ℚ) - ((r : ℚ) + e)) <
          2 * ((d : ℚ) ^ 2 + 2 * d * n - (n : ℚ) ^ 2) + 2 * n - 1 + 1 := by
        linarith only [hs, R4, hn1', hκ2]
      have key' : (d + n) * (z.1 - (r - e)) + (d - n) * (z.2 - (r + e)) < 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 1 + 1 := by
        exact_mod_cast key
      linarith only [key']
  have hev : decide ((z.1 - (r - e) + (z.2 - (r + e))) % 2 = 0) = false := by
    rw [decide_eq_false_iff_not]; omega
  have hmu : muOf ⟨n, d⟩ = 2 := by
    show (if (n + d) % 2 = 1 then 2 else 1) = 2
    rw [if_pos (by omega)]
  rw [inH_P_iff d n _ false hev hmu]
  have hA' : aOf ⟨n, d⟩ false = n := rfl
  have hl' : lOf ⟨n, d⟩ false = min (d - n) (3 * n - d) := rfl
  rw [hA', hl']
  dsimp only
  refine ⟨by linarith only [hTlo], by linarith only [hThi], by linarith only [hSlo], by linarith only [hShi]⟩

/-- The generic even lower `t` bound of the `P@V_Q` box (for `(e, r) ≠ (3, 1)`). -/
theorem PVQ_lo_gen (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (hnot : ¬ (e = 3 ∧ r = 1))
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (d : ℚ) - n)
    (hu0 : 0 ≤ u) (hu1 : u ≤ α) (hv0 : β ≤ v) (hv1 : v ≤ 1) (m : ℤ) (hm : m = min (2 * n) (d - n)) :
    m - (d ^ 2 + 2 * d * n - n ^ 2) - 1 < n * (z.1 - (r - e)) - d * (z.2 - (r + e)) := by
  have hdet' := hdet
  obtain ⟨hα0, hα1, hβ0, hβ1, hκ0, hκ1, hW⟩ := box_pos_W0 d n e r hn hnd hr hre hdet α β κ hα hβ hκ
  have hDne : (d : ℚ) + e ≠ 0 := by
    have : (0 : ℤ) < d + e := by omega
    exact ne_of_gt (by exact_mod_cast this)
  obtain ⟨hαβ, hA, hB⟩ := ab_PW0 d n e r hdet α β κ hDne hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := pvq_real (((d : ℚ) + n) / 2) (n : ℚ) (KP d n e r) (TP d n) α β κ u v hW hA hB hu0 hu1 hv0 hv1
  have ht := t_PVQ d n e r hdet z u v hz1 hz2
  have heven_a := even_alpha d n e r hn hnd hr hre hdet hnot hodd α hα m hm
  unfold KP TP at R2 ht
  have hlo : ((m : ℤ) : ℚ) - (((d : ℚ) ^ 2 + 2 * d * n - (n : ℚ) ^ 2)) - 1 <
      (n : ℚ) * ((z.1 : ℚ) - ((r : ℚ) - e)) - (d : ℚ) * ((z.2 : ℚ) - ((r : ℚ) + e)) := by
    rw [ht]; linarith only [R2, heven_a]
  have h : ((m - (d ^ 2 + 2 * d * n - n ^ 2) - 1 : ℤ) : ℚ) < ((n * (z.1 - (r - e)) - d * (z.2 - (r + e)) : ℤ) : ℚ) := by
    push_cast; linarith only [hlo]
  exact_mod_cast h

/-- The core inequality of the `(3,1)` case: `2u + (14n²+22n+5)v < 14n²+22n+13/2` from `uX ≤ 3n+1`, `vY ≤ Y − 1`. -/
theorem pvq31_core (n u v : ℚ) (hn : 1 ≤ n) (hu : u * (3 * n + 4) ≤ 3 * n + 1)
    (hv : (28 * n ^ 2 + 72 * n + 46) * v ≤ 28 * n ^ 2 + 72 * n + 45) :
    2 * u + (14 * n ^ 2 + 22 * n + 5) * v < 14 * n ^ 2 + 22 * n + 13 / 2 := by
  have hX : 0 < 3 * n + 4 := by linarith
  have hY : 0 < 28 * n ^ 2 + 72 * n + 46 := by nlinarith
  have hC : 0 ≤ 14 * n ^ 2 + 22 * n + 5 := by nlinarith
  have hpoly : 2 * (3 * n + 1) * (28 * n ^ 2 + 72 * n + 46) + (14 * n ^ 2 + 22 * n + 5) * ((28 * n ^ 2 + 72 * n + 46) - 1) * (3 * n + 4) <
      (14 * n ^ 2 + 22 * n + 13 / 2) * (3 * n + 4) * (28 * n ^ 2 + 72 * n + 46) := by
    nlinarith [sq_nonneg n]
  have h1 : 2 * (u * (3 * n + 4)) * (28 * n ^ 2 + 72 * n + 46) ≤ 2 * (3 * n + 1) * (28 * n ^ 2 + 72 * n + 46) := by
    have := mul_le_mul_of_nonneg_right hu hY.le
    linarith
  have hv' : v * (28 * n ^ 2 + 72 * n + 46) ≤ 28 * n ^ 2 + 72 * n + 46 - 1 := by linarith
  have h2 : (14 * n ^ 2 + 22 * n + 5) * (v * (28 * n ^ 2 + 72 * n + 46)) * (3 * n + 4) ≤
      (14 * n ^ 2 + 22 * n + 5) * ((28 * n ^ 2 + 72 * n + 46) - 1) * (3 * n + 4) := by
    have := mul_le_mul_of_nonneg_left hv' hC
    have := mul_le_mul_of_nonneg_right this hX.le
    linarith
  have key : (2 * u + (14 * n ^ 2 + 22 * n + 5) * v) * ((3 * n + 4) * (28 * n ^ 2 + 72 * n + 46)) <
      (14 * n ^ 2 + 22 * n + 13 / 2) * ((3 * n + 4) * (28 * n ^ 2 + 72 * n + 46)) := by
    linarith
  exact lt_of_mul_lt_mul_right key (by positivity)

/-- The `(3,1)` even lower `t` bound of the `P@V_Q` box, with `d = 3n + 1`: integrality gives `N = 82 v`-type bound `v < 1 ⇒ N ≤ 2T_X − 1`. -/
theorem PVQ_lo_31 (d n : ℤ) (hn : 1 ≤ n) (hd : d = 3 * n + 1) (z : ℤ × ℤ) (α u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + 3)) + v * ((n : ℚ) + 1 - ((d : ℚ) + 3)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + 1)) + v * ((d : ℚ) + 3 + ((n : ℚ) + 1)))
    (hα : α * ((d : ℚ) + 3) = d) (hu1 : u ≤ α) (_hv0 : 0 ≤ v) (hv1 : v < 1) (m : ℤ) (hm : m = min (2 * n) (d - n)) :
    m - (d ^ 2 + 2 * d * n - n ^ 2) - 1 < n * (z.1 - (1 - 3)) - d * (z.2 - (1 + 3)) := by
  subst hd
  have hm2 : m = 2 * n := by omega
  subst hm2
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hα' : α * (3 * (n : ℚ) + 4) = 3 * n + 1 := by
    have : ((3 * n + 1 : ℤ) : ℚ) = 3 * (n : ℚ) + 1 := by push_cast; ring
    rw [← this]
    have h3 : (((3 * n + 1 : ℤ) : ℚ) + 3) = 3 * (n : ℚ) + 4 := by push_cast; ring
    rw [← h3]
    exact hα
  have hN : (((6 * n + 8) * z.2 - (2 * n + 2) * z.1 + 4 * n + 5 : ℤ) : ℚ) = (28 * (n : ℚ) ^ 2 + 72 * n + 46) * v := by
    push_cast at hz1 hz2 ⊢
    linear_combination (6 * (n : ℚ) + 8) * hz2 - (2 * (n : ℚ) + 2) * hz1
  have hNlt : (6 * n + 8) * z.2 - (2 * n + 2) * z.1 + 4 * n + 5 < 28 * n ^ 2 + 72 * n + 46 := by
    have hY : (0 : ℚ) < 28 * (n : ℚ) ^ 2 + 72 * n + 46 := by positivity
    have : (((6 * n + 8) * z.2 - (2 * n + 2) * z.1 + 4 * n + 5 : ℤ) : ℚ) < ((28 * n ^ 2 + 72 * n + 46 : ℤ) : ℚ) := by
      rw [hN]; push_cast; nlinarith only [hv1, hY]
    exact_mod_cast this
  have hNle : (6 * n + 8) * z.2 - (2 * n + 2) * z.1 + 4 * n + 5 ≤ 28 * n ^ 2 + 72 * n + 45 := by
    have : (6 * n + 8) * z.2 - (2 * n + 2) * z.1 + 4 * n + 5 < 28 * n ^ 2 + 72 * n + 46 := hNlt
    linarith
  have hNle' : (((6 * n + 8) * z.2 - (2 * n + 2) * z.1 + 4 * n + 5 : ℤ) : ℚ) ≤ ((28 * n ^ 2 + 72 * n + 45 : ℤ) : ℚ) := by
    exact_mod_cast hNle
  have hv' : (28 * (n : ℚ) ^ 2 + 72 * n + 46) * v ≤ 28 * (n : ℚ) ^ 2 + 72 * n + 45 := by
    rw [← hN]; exact_mod_cast hNle
  have hu' : u * (3 * (n : ℚ) + 4) ≤ 3 * n + 1 := by
    have hX : (0 : ℚ) ≤ 3 * n + 4 := by positivity
    have := mul_le_mul_of_nonneg_right hu1 hX
    linarith
  have key := pvq31_core (n : ℚ) u v hnq hu' hv'
  have hreal : (((n * (z.1 - (1 - 3)) - (3 * n + 1) * (z.2 - (1 + 3)) : ℤ)) : ℚ) =
      16 * (n : ℚ) + 9 / 2 - 2 * u - (14 * (n : ℚ) ^ 2 + 22 * n + 5) * v := by
    push_cast at hz1 hz2 ⊢
    linear_combination (n : ℚ) * hz1 - (3 * (n : ℚ) + 1) * hz2
  have h : ((2 * n - ((3 * n + 1) ^ 2 + 2 * (3 * n + 1) * n - n ^ 2) - 1 : ℤ) : ℚ) <
      (((n * (z.1 - (1 - 3)) - (3 * n + 1) * (z.2 - (1 + 3)) : ℤ)) : ℚ) := by
    rw [hreal]; push_cast; linarith only [key]
  exact_mod_cast h

/-- Even sites of the `P@V_Q` box, given the lower `t` bound `hlo`. -/
theorem inH_PVQ_even_of_lo (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (d : ℚ) - n)
    (hu0 : 0 ≤ u) (hu1 : u ≤ α) (hv0 : β ≤ v) (hv1 : v ≤ 1) (hpar : (z.1 + z.2) % 2 = 0)
    (m : ℤ) (hm : m = min (2 * n) (d - n))
    (hlo : m - (d ^ 2 + 2 * d * n - n ^ 2) - 1 < n * (z.1 - (r - e)) - d * (z.2 - (r + e))) :
    InH ⟨n, d⟩ (z.1 - (r - e), z.2 - (r + e)) := by
  obtain ⟨hα0, hα1, hβ0, hβ1, hκ0, hκ1, hW⟩ := box_pos_W0 d n e r hn hnd hr hre hdet α β κ hα hβ hκ
  have hDne : (d : ℚ) + e ≠ 0 := by
    have : (0 : ℤ) < d + e := by omega
    exact ne_of_gt (by exact_mod_cast this)
  obtain ⟨hαβ, hA, hB⟩ := ab_PW0 d n e r hdet α β κ hDne hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := pvq_real (((d : ℚ) + n) / 2) (n : ℚ) (KP d n e r) (TP d n) α β κ u v hW hA hB hu0 hu1 hv0 hv1
  have ht := t_PVQ d n e r hdet z u v hz1 hz2
  have hs := s_PVQ d n e r hdet z u v hz1 hz2
  unfold KP TP at R1 R3 R4 ht hs
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hm2 : 2 * m ≤ n + d := by omega
  have hm2q : 2 * (m : ℚ) ≤ (n : ℚ) + d := by exact_mod_cast hm2
  have hThi : n * (z.1 - (r - e)) - d * (z.2 - (r + e)) < d + n - m + 1 := by
    have h : ((n * (z.1 - (r - e)) - d * (z.2 - (r + e)) : ℤ) : ℚ) < ((d + n - m + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith only [R1, hκ1, hm2q]
    exact_mod_cast h
  have hSlo : -1 < (d + n) * (z.1 - (r - e)) + (d - n) * (z.2 - (r + e)) := by
    have h : ((-1 : ℤ) : ℚ) < (((d + n) * (z.1 - (r - e)) + (d - n) * (z.2 - (r + e)) : ℤ) : ℚ) := by
      push_cast; rw [hs]; linarith only [R3, hβ0, hnq]
    exact_mod_cast h
  have hShi : (d + n) * (z.1 - (r - e)) + (d - n) * (z.2 - (r + e)) < 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n + 1 := by
    have h : (((d + n) * (z.1 - (r - e)) + (d - n) * (z.2 - (r + e)) : ℤ) : ℚ) <
        ((2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n + 1 : ℤ) : ℚ) := by
      push_cast; rw [hs]; linarith only [R4, hκ1, hnq]
    exact_mod_cast h
  have hev : decide ((z.1 - (r - e) + (z.2 - (r + e))) % 2 = 0) = true := by
    rw [decide_eq_true_iff]; omega
  have hmu : muOf ⟨n, d⟩ = 2 := by
    show (if (n + d) % 2 = 1 then 2 else 1) = 2
    rw [if_pos (by omega)]
  rw [inH_P_iff d n _ true hev hmu]
  have hA' : aOf ⟨n, d⟩ true = m := by rw [hm]; rfl
  have hl' : lOf ⟨n, d⟩ true = 0 := rfl
  rw [hA', hl']
  dsimp only
  refine ⟨by linarith only [hlo], by linarith only [hThi], by linarith only [hSlo], by linarith only [hShi]⟩

/-- The `P` source at `z − V_Q` on the box `[0, α] × [β, 1]` (W0), both parities and both `(e, r)`. -/
theorem PVQ_box_W0 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (d : ℚ) - n)
    (hu0 : 0 ≤ u) (hu1 : u ≤ α) (hv0 : β ≤ v) (hv1 : v ≤ 1) :
    InH ⟨n, d⟩ (z.1 - (r - e), z.2 - (r + e)) := by
  rcases Int.emod_two_eq_zero_or_one (z.1 + z.2) with hpar | hpar
  · by_cases hx : e = 3 ∧ r = 1
    · obtain ⟨he, hr1⟩ := hx
      subst he
      subst hr1
      obtain ⟨-, -, hβ0, -, -, -, -⟩ := box_pos_W0 d n 3 1 hn hnd hr hre hdet α β κ hα hβ hκ
      have hd : d = 3 * n + 1 := by omega
      -- v = 1 is impossible at integer points: N = 2T_X v would be even, but N is odd
      have hv1' : v < 1 := by
        rcases hv1.lt_or_eq with h | h
        · exact h
        · exfalso
          have hN : (((6 * n + 8) * z.2 - (2 * n + 2) * z.1 + 4 * n + 5 : ℤ) : ℚ) = 28 * (n : ℚ) ^ 2 + 72 * n + 46 := by
            subst hd
            have hz1' := hz1
            have hz2' := hz2
            push_cast at hz1' hz2' ⊢
            rw [h] at hz1' hz2'
            linear_combination (6 * (n : ℚ) + 8) * hz2' - (2 * (n : ℚ) + 2) * hz1'
          have hNint : (6 * n + 8) * z.2 - (2 * n + 2) * z.1 + 4 * n + 5 = 28 * n ^ 2 + 72 * n + 46 := by
            exact_mod_cast hN
          have hpar2 : (6 * n + 8) * z.2 - (2 * n + 2) * z.1 + 4 * n + 5 =
              2 * ((3 * n + 4) * z.2 - (n + 1) * z.1) + (4 * n + 5) := by ring
          have hodd2 : ((3 * n + 4) * z.2 - (n + 1) * z.1) = (3 * n + 4) * z.2 - (n + 1) * z.1 := rfl
          have h28 : 28 * n ^ 2 + 72 * n + 46 = 2 * (14 * n ^ 2 + 36 * n + 23) := by ring
          rw [hpar2, h28] at hNint
          omega
      have hlo := PVQ_lo_31 d n (by omega) hd z α u v (by push_cast at hz1 ⊢; exact hz1) (by push_cast at hz2 ⊢; exact hz2)
        (by push_cast at hα ⊢; exact hα) hu1 (by linarith) hv1' (min (2 * n) (d - n)) rfl
      exact inH_PVQ_even_of_lo d n 3 1 hn hnd hr hre hdet hodd heven z α β κ u v hz1 hz2 hα hβ hκ hu0 hu1 hv0
        hv1 hpar (min (2 * n) (d - n)) rfl hlo
    · have hlo := PVQ_lo_gen d n e r hn hnd hr hre hdet hodd hx z α β κ u v hz1 hz2 hα hβ hκ hu0 hu1 hv0 hv1
        (min (2 * n) (d - n)) rfl
      exact inH_PVQ_even_of_lo d n e r hn hnd hr hre hdet hodd heven z α β κ u v hz1 hz2 hα hβ hκ hu0 hu1 hv0
        hv1 hpar (min (2 * n) (d - n)) rfl hlo
  · exact inH_PVQ_odd d n e r hn hnd hr hre hdet hodd heven z α β κ u v hz1 hz2 hα hβ hκ hu0 hu1 hv0 hv1 hpar

end FLatticePaper.Tiles.PairW0P



