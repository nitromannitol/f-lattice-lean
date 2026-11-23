import FLatticePaper.Tiles.PairQAbox

/-! Task 53, item 2 (covering reduction), section 11: the `Q` box of the flag-false odd child (W0, `δ = dr − ne = +1`).

The box `[0, β]²` of the cell (`β = e/D`, `D = d + e`) is covered by the two copies `Q@0` (the point `z`) and `Q@Q` (the point
`z − (e, r)`). The owner is decided by the integer test `s_Q(z) ≤ T_Q + 2r − l` (the upper `s` facet of `Q@0`): if it holds,
`Q@0` owns `z`; otherwise `Q@Q` does. The `t` facets are the same for both copies and hold on the whole box; when the test fails,
`s_Q(z) − T_Q ≥ 2r − l + 1 ≥ l` and `s_Q(z) − T_Q ≤ T_Q + 2r − l` hold by the real bounds.

With `K = s_Q(P)`, `T = T_Q`, `W = K + T`, `κ = (e−r)/D`: `t_Q(z) = (e+r)/2 + 2u − W v`, `s_Q(z) = r + 2W u − 2v`,
and `β W = T − κ` (from `βK − αT = −κ`, a consequence of `δ = +1`).
The reflection about the centre `c = (r+1, e+2r−1)` (a centre of symmetry of the window of `Q`) sends `Q@0` and `Q@Q` to the
copies `Q@(2P+V_P+Q)` and `Q@(2P+V_P)` on the reflected box `[α, 1]²`. -/

namespace FLatticePaper.Tiles.PairW0Q

open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.PairQAbox

/-- `βK − αT = −κ` for the Q window with `δ = +1`. -/
theorem ab_QW0 (d n e r : ℤ) (hdet : d * r - n * e = 1) (α β κ : ℚ) (hD : (d : ℚ) + e ≠ 0)
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r) :
    α + β = 1 ∧ β * Kq d n e r - α * Tq e r = -κ := by
  have hdetQ : (d : ℚ) * r - n * e = 1 := by exact_mod_cast hdet
  have h1 : α + β = 1 := by
    have : (α + β) * ((d : ℚ) + e) = 1 * ((d : ℚ) + e) := by linear_combination hα + hβ
    exact mul_right_cancel₀ hD this
  refine ⟨h1, ?_⟩
  have h2 : (β * Kq d n e r - α * Tq e r) * ((d : ℚ) + e) = (-κ) * ((d : ℚ) + e) := by
    unfold Kq Tq
    linear_combination (((e : ℚ) + r) * d + ((e : ℚ) - r) * n) * hβ
      - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) * hα + hκ - ((e : ℚ) - r) * hdetQ
  exact mul_right_cancel₀ hD h2

/-- `t_Q(z)` for the Q window at the point `z` (W0). -/
theorem t_Q0 (d n e r : ℤ) (hdet : d * r - n * e = 1) (z : ℤ × ℤ) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r))) :
    (r : ℚ) * (z.1 : ℚ) - (e : ℚ) * (z.2 : ℚ) = ((e : ℚ) + r) / 2 + 2 * u - (Kq d n e r + Tq e r) * v := by
  have hdetQ : (d : ℚ) * r - n * e = 1 := by exact_mod_cast hdet
  unfold Kq Tq
  linear_combination (r : ℚ) * hz1 - (e : ℚ) * hz2 + 2 * u * hdetQ

/-- `s_Q(z)` for the Q window at the point `z` (W0). -/
theorem s_Q0 (d n e r : ℤ) (hdet : d * r - n * e = 1) (z : ℤ × ℤ) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r))) :
    ((e : ℚ) + r) * (z.1 : ℚ) + ((e : ℚ) - r) * (z.2 : ℚ) = r + 2 * (Kq d n e r + Tq e r) * u - 2 * v := by
  have hdetQ : (d : ℚ) * r - n * e = 1 := by exact_mod_cast hdet
  unfold Kq Tq
  linear_combination ((e : ℚ) + r) * hz1 + ((e : ℚ) - r) * hz2 - 2 * v * hdetQ

/-- The four real facets of the `Q` window on the box `[0, β]²` (W0), for `t` and for `s` (copy `Q@0`). -/
theorem Q0_real (E R K T α β κ u v : ℚ) (hW : 0 ≤ K + T) (hαβ : α + β = 1) (hK : β * K - α * T = -κ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hv0 : 0 ≤ v) (hv1 : v ≤ β) :
    (E + R) / 2 + 2 * u - (K + T) * v ≤ (E + R) / 2 + 2 * β ∧
    (E + R) / 2 - T + κ ≤ (E + R) / 2 + 2 * u - (K + T) * v ∧
    R - 2 * β ≤ R + 2 * (K + T) * u - 2 * v ∧
    R + 2 * (K + T) * u - 2 * v ≤ R + 2 * T - 2 * κ := by
  have hWβ : (K + T) * β = T - κ := by linear_combination hK + T * hαβ
  have hWv1 : (K + T) * v ≤ (K + T) * β := mul_le_mul_of_nonneg_left hv1 hW
  have hWv0 : 0 ≤ (K + T) * v := mul_nonneg hW hv0
  have hWu1 : (K + T) * u ≤ (K + T) * β := mul_le_mul_of_nonneg_left hu1 hW
  have hWu0 : 0 ≤ (K + T) * u := mul_nonneg hW hu0
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Positivity of the Q-box variables (W0). -/
theorem box_pos_Q0 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (α β κ : ℚ) (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r) :
    0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧ 0 ≤ κ ∧ κ < 1 ∧ 0 ≤ Kq d n e r + Tq e r := by
  have hDi : (0 : ℤ) < d + e := by omega
  have hDq : (0 : ℚ) < (d : ℚ) + e := by exact_mod_cast hDi
  have hdq : (0 : ℚ) < d := by exact_mod_cast (show (0 : ℤ) < d by omega)
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  have heq : (r : ℚ) < e := by exact_mod_cast hre
  have hndq : (n : ℚ) < d := by exact_mod_cast hnd
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
  unfold Kq Tq
  nlinarith

/-- `e ≠ 2r` for W0 (from `dr − ne = 1` and the parity of `e + r`). -/
theorem e_ne_two_r_W0 (d n e r : ℤ) (hr : 0 < r) (hdet : d * r - n * e = 1) (heven : (e + r) % 2 = 0) :
    e ≠ 2 * r := by
  intro h
  subst h
  have h1 : r * (d - 2 * n) = 1 := by linarith
  have hpos : 0 < d - 2 * n := by
    by_contra hc
    push Not at hc
    nlinarith
  have h2 : 1 ≤ d - 2 * n := by omega
  have h3 : r * 1 ≤ r * (d - 2 * n) := mul_le_mul_of_nonneg_left h2 hr.le
  have h4 : r = 1 := by linarith
  omega

/-- The odd copy `Q@0` (the point `z` itself): the test `s_Q(z) ≤ T + 2r − L` holds. -/
theorem inH_Q0_odd_copy1 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hv0 : 0 ≤ v) (hv1 : v ≤ β) (hpar : (z.1 + z.2) % 2 = 1)
    (L : ℤ) (hL : L = min (e - r) (3 * r - e))
    (htest : (e + r) * z.1 + (e - r) * z.2 ≤ e ^ 2 + 2 * e * r - r ^ 2 + 2 * r - L) :
    InH ⟨r, e⟩ z := by
  obtain ⟨hα0, hα1, hβ0, hβ1, hκ0, hκ1, hW⟩ := box_pos_Q0 d n e r hn hnd hr hre α β κ hα hβ hκ
  have hDne : (d : ℚ) + e ≠ 0 := by
    have : (0 : ℤ) < d + e := by omega
    exact ne_of_gt (by exact_mod_cast this)
  obtain ⟨hαβ, hK⟩ := ab_QW0 d n e r hdet α β κ hDne hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := Q0_real (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW hαβ hK hu0 hu1 hv0 hv1
  have ht := t_Q0 d n e r hdet z u v hz1 hz2
  have hs := s_Q0 d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R1 R2 R3 R4 ht hs
  have hE2 : (2 : ℚ) ≤ (e : ℚ) - r := by
    have h : (2 : ℤ) ≤ e - r := by omega
    exact_mod_cast h
  have hne := e_ne_two_r_W0 d n e r hr hdet heven
  have hLle : L ≤ r - 1 := by omega
  have hLq : (L : ℚ) ≤ (r : ℚ) - 1 := by exact_mod_cast hLle
  have htestq : ((e : ℚ) + r) * (z.1 : ℚ) + ((e : ℚ) - r) * (z.2 : ℚ) ≤ (e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2 + 2 * r - L := by
    exact_mod_cast htest
  have hev : decide ((z.1 + z.2) % 2 = 0) = false := by
    rw [decide_eq_false_iff_not]; omega
  have hmu : muOf ⟨r, e⟩ = 1 := by
    show (if (r + e) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  rw [inH_Q_iff r e z false hev hmu]
  have hA : aOf ⟨r, e⟩ false = r := rfl
  have hl : lOf ⟨r, e⟩ false = L := by rw [hL]; rfl
  rw [hA, hl]
  have G1 : r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * z.1 - e * z.2 := by
    have h : ((r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) < ((r * z.1 - e * z.2 : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith only [R2, hE2, hκ0]
    exact_mod_cast h
  have G2 : r * z.1 - e * z.2 < e + r - r + 1 := by
    have h : ((r * z.1 - e * z.2 : ℤ) : ℚ) < ((e + r - r + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith only [R1, hE2, hβ1]
    exact_mod_cast h
  have G3 : L - 1 < (e + r) * z.1 + (e - r) * z.2 := by
    have h : ((L - 1 : ℤ) : ℚ) < (((e + r) * z.1 + (e - r) * z.2 : ℤ) : ℚ) := by
      push_cast; rw [hs]; linarith only [R3, hLq, hβ1]
    exact_mod_cast h
  refine ⟨by linarith only [G1], by linarith only [G2], by linarith only [G3], by linarith only [htest]⟩

/-- The odd copy `Q@0` fails its test: the second copy `Q@Q` owns `z`. -/
theorem inH_Q0_odd_copy2 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hv0 : 0 ≤ v) (hv1 : v ≤ β) (hpar : (z.1 + z.2) % 2 = 1)
    (L : ℤ) (hL : L = min (e - r) (3 * r - e))
    (htest : e ^ 2 + 2 * e * r - r ^ 2 + 2 * r - L < (e + r) * z.1 + (e - r) * z.2) :
    InH ⟨r, e⟩ (z.1 - e, z.2 - r) := by
  obtain ⟨hα0, hα1, hβ0, hβ1, hκ0, hκ1, hW⟩ := box_pos_Q0 d n e r hn hnd hr hre α β κ hα hβ hκ
  have hDne : (d : ℚ) + e ≠ 0 := by
    have : (0 : ℤ) < d + e := by omega
    exact ne_of_gt (by exact_mod_cast this)
  obtain ⟨hαβ, hK⟩ := ab_QW0 d n e r hdet α β κ hDne hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := Q0_real (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW hαβ hK hu0 hu1 hv0 hv1
  have ht := t_Q0 d n e r hdet z u v hz1 hz2
  have hs := s_Q0 d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R1 R2 R3 R4 ht hs
  have ht' : (r : ℚ) * ((z.1 : ℚ) - e) - (e : ℚ) * ((z.2 : ℚ) - r) = (r : ℚ) * (z.1 : ℚ) - (e : ℚ) * (z.2 : ℚ) := by ring
  have hs' : ((e : ℚ) + r) * ((z.1 : ℚ) - e) + ((e : ℚ) - r) * ((z.2 : ℚ) - r) =
      ((e : ℚ) + r) * (z.1 : ℚ) + ((e : ℚ) - r) * (z.2 : ℚ) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) := by ring
  have hE2 : (2 : ℚ) ≤ (e : ℚ) - r := by
    have h : (2 : ℤ) ≤ e - r := by omega
    exact_mod_cast h
  have hne := e_ne_two_r_W0 d n e r hr hdet heven
  have hLle : L ≤ r - 1 := by omega
  have hLq : (L : ℚ) ≤ (r : ℚ) - 1 := by exact_mod_cast hLle
  have htestq : (e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2 + 2 * r - L < ((e : ℚ) + r) * (z.1 : ℚ) + ((e : ℚ) - r) * (z.2 : ℚ) := by
    exact_mod_cast htest
  have hev : decide ((z.1 - e + (z.2 - r)) % 2 = 0) = false := by
    rw [decide_eq_false_iff_not]; omega
  have hmu : muOf ⟨r, e⟩ = 1 := by
    show (if (r + e) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  rw [inH_Q_iff r e _ false hev hmu]
  have hA : aOf ⟨r, e⟩ false = r := rfl
  have hl : lOf ⟨r, e⟩ false = L := by rw [hL]; rfl
  rw [hA, hl]
  dsimp only
  have G1 : r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * (z.1 - e) - e * (z.2 - r) := by
    have h : ((r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) < ((r * (z.1 - e) - e * (z.2 - r) : ℤ) : ℚ) := by
      push_cast; rw [ht', ht]; linarith only [R2, hE2, hκ0]
    exact_mod_cast h
  have G2 : r * (z.1 - e) - e * (z.2 - r) < e + r - r + 1 := by
    have h : ((r * (z.1 - e) - e * (z.2 - r) : ℤ) : ℚ) < ((e + r - r + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht', ht]; linarith only [R1, hE2, hβ1]
    exact_mod_cast h
  have G3 : L ≤ (e + r) * (z.1 - e) + (e - r) * (z.2 - r) := by
    have h : (L : ℚ) - 1 < (((e + r) * (z.1 - e) + (e - r) * (z.2 - r) : ℤ) : ℚ) := by
      push_cast; rw [hs']; linarith only [htestq, hLq, hκ0, hβ1]
    have h' : L - 1 < (e + r) * (z.1 - e) + (e - r) * (z.2 - r) := by exact_mod_cast h
    linarith only [h']
  have G4 : (e + r) * (z.1 - e) + (e - r) * (z.2 - r) < 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - L + 1 := by
    have h : (((e + r) * (z.1 - e) + (e - r) * (z.2 - r) : ℤ) : ℚ) <
        ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - L + 1 : ℤ) : ℚ) := by
      push_cast; rw [hs']; linarith only [R4, hs, hLq, hκ0]
    exact_mod_cast h
  refine ⟨by linarith only [G1], by linarith only [G2], by linarith only [G3], by linarith only [G4]⟩

/-- The even copy `Q@0` (the point `z` itself): the test `s_Q(z) ≤ T + 2r` holds. -/
theorem inH_Q0_even_copy1 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (heven : (e + r) % 2 = 0) (hexc : e = 3 * r → e < d)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hv0 : 0 ≤ v) (hv1 : v ≤ β) (hpar : (z.1 + z.2) % 2 = 0)
    (A : ℤ) (hA : A = min (2 * r) (e - r))
    (htest : (e + r) * z.1 + (e - r) * z.2 ≤ e ^ 2 + 2 * e * r - r ^ 2 + 2 * r) :
    InH ⟨r, e⟩ z := by
  obtain ⟨hα0, hα1, hβ0, hβ1, hκ0, hκ1, hW⟩ := box_pos_Q0 d n e r hn hnd hr hre α β κ hα hβ hκ
  have hDne : (d : ℚ) + e ≠ 0 := by
    have : (0 : ℤ) < d + e := by omega
    exact ne_of_gt (by exact_mod_cast this)
  obtain ⟨hαβ, hK⟩ := ab_QW0 d n e r hdet α β κ hDne hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := Q0_real (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW hαβ hK hu0 hu1 hv0 hv1
  have ht := t_Q0 d n e r hdet z u v hz1 hz2
  have hs := s_Q0 d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R1 R2 R3 R4 ht hs
  have hrq : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hAle : 2 * A ≤ e + r := by omega
  have hAq : 2 * (A : ℚ) ≤ (e : ℚ) + r := by exact_mod_cast hAle
  have hev : decide ((z.1 + z.2) % 2 = 0) = true := by
    rw [decide_eq_true_iff]; omega
  have hmu : muOf ⟨r, e⟩ = 1 := by
    show (if (r + e) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  rw [inH_Q_iff r e z true hev hmu]
  have hA' : aOf ⟨r, e⟩ true = A := by rw [hA]; rfl
  have hl : lOf ⟨r, e⟩ true = 0 := rfl
  rw [hA', hl]
  have G1 : A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * z.1 - e * z.2 := by
    have h : ((A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) < ((r * z.1 - e * z.2 : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith only [R2, hAq, hκ0]
    exact_mod_cast h
  have G2 : r * z.1 - e * z.2 < e + r - A + 1 := by
    have h : ((r * z.1 - e * z.2 : ℤ) : ℚ) < ((e + r - A + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht]
      rcases (show e ≥ 3 * r + 2 ∨ e ≤ 3 * r - 2 ∨ e = 3 * r by omega) with h3 | h3 | h3
      · have hA2 : A = 2 * r := by omega
        have h3q : (3 * (r : ℚ) + 2) ≤ e := by exact_mod_cast h3
        rw [hA2]; push_cast
        linarith only [R1, h3q, hβ0, hβ1]
      · have hA2 : A = e - r := by omega
        have h3q : (e : ℚ) ≤ 3 * r - 2 := by exact_mod_cast h3
        rw [hA2]; push_cast
        linarith only [R1, h3q, hβ0, hβ1]
      · have hA2 : A = 2 * r := by omega
        have hedq : (e : ℚ) < d := by exact_mod_cast hexc h3
        have hDpos : (0 : ℚ) < (d : ℚ) + e := by
          have : (0 : ℤ) < d + e := by omega
          exact_mod_cast this
        have hβh : 2 * β < 1 := by
          have hβD : β * ((d : ℚ) + e) = e := hβ
          nlinarith only [hβD, hedq, hDpos, hβ0]
        have h3q : (e : ℚ) = 3 * r := by exact_mod_cast h3
        rw [hA2]; push_cast
        linarith only [R1, h3q, hβh, hκ0]
    exact_mod_cast h
  have G3 : -1 < (e + r) * z.1 + (e - r) * z.2 := by
    have h : ((-1 : ℤ) : ℚ) < (((e + r) * z.1 + (e - r) * z.2 : ℤ) : ℚ) := by
      push_cast; rw [hs]; linarith only [R3, hβ1, hrq]
    exact_mod_cast h
  refine ⟨by linarith only [G1], by linarith only [G2], by linarith only [G3], by linarith only [htest]⟩

/-- The even copy `Q@Q` (the point `z − (e, r)`): the test `s_Q(z) ≤ T + 2r` fails. -/
theorem inH_Q0_even_copy2 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (heven : (e + r) % 2 = 0) (hexc : e = 3 * r → e < d)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hv0 : 0 ≤ v) (hv1 : v ≤ β) (hpar : (z.1 + z.2) % 2 = 0)
    (A : ℤ) (hA : A = min (2 * r) (e - r))
    (htest : e ^ 2 + 2 * e * r - r ^ 2 + 2 * r < (e + r) * z.1 + (e - r) * z.2) :
    InH ⟨r, e⟩ (z.1 - e, z.2 - r) := by
  obtain ⟨hα0, hα1, hβ0, hβ1, hκ0, hκ1, hW⟩ := box_pos_Q0 d n e r hn hnd hr hre α β κ hα hβ hκ
  have hDne : (d : ℚ) + e ≠ 0 := by
    have : (0 : ℤ) < d + e := by omega
    exact ne_of_gt (by exact_mod_cast this)
  obtain ⟨hαβ, hK⟩ := ab_QW0 d n e r hdet α β κ hDne hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := Q0_real (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW hαβ hK hu0 hu1 hv0 hv1
  have ht := t_Q0 d n e r hdet z u v hz1 hz2
  have hs := s_Q0 d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R1 R2 R3 R4 ht hs
  have ht' : (r : ℚ) * ((z.1 : ℚ) - e) - (e : ℚ) * ((z.2 : ℚ) - r) = (r : ℚ) * (z.1 : ℚ) - (e : ℚ) * (z.2 : ℚ) := by ring
  have hs' : ((e : ℚ) + r) * ((z.1 : ℚ) - e) + ((e : ℚ) - r) * ((z.2 : ℚ) - r) =
      ((e : ℚ) + r) * (z.1 : ℚ) + ((e : ℚ) - r) * (z.2 : ℚ) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) := by ring
  have hrq : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hAle : 2 * A ≤ e + r := by omega
  have hAq : 2 * (A : ℚ) ≤ (e : ℚ) + r := by exact_mod_cast hAle
  have htestq : (e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2 + 2 * r < ((e : ℚ) + r) * (z.1 : ℚ) + ((e : ℚ) - r) * (z.2 : ℚ) := by
    exact_mod_cast htest
  have hev : decide ((z.1 - e + (z.2 - r)) % 2 = 0) = true := by
    rw [decide_eq_true_iff]; omega
  have hmu : muOf ⟨r, e⟩ = 1 := by
    show (if (r + e) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  rw [inH_Q_iff r e _ true hev hmu]
  have hA' : aOf ⟨r, e⟩ true = A := by rw [hA]; rfl
  have hl : lOf ⟨r, e⟩ true = 0 := rfl
  rw [hA', hl]
  dsimp only
  have G1 : A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * (z.1 - e) - e * (z.2 - r) := by
    have h : ((A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) < ((r * (z.1 - e) - e * (z.2 - r) : ℤ) : ℚ) := by
      push_cast; rw [ht', ht]; linarith only [R2, hAq, hκ0]
    exact_mod_cast h
  have G2 : r * (z.1 - e) - e * (z.2 - r) < e + r - A + 1 := by
    have h : ((r * (z.1 - e) - e * (z.2 - r) : ℤ) : ℚ) < ((e + r - A + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht', ht]
      rcases (show e ≥ 3 * r + 2 ∨ e ≤ 3 * r - 2 ∨ e = 3 * r by omega) with h3 | h3 | h3
      · have hA2 : A = 2 * r := by omega
        have h3q : (3 * (r : ℚ) + 2) ≤ e := by exact_mod_cast h3
        rw [hA2]; push_cast
        linarith only [R1, h3q, hβ0, hβ1]
      · have hA2 : A = e - r := by omega
        have h3q : (e : ℚ) ≤ 3 * r - 2 := by exact_mod_cast h3
        rw [hA2]; push_cast
        linarith only [R1, h3q, hβ0, hβ1]
      · have hA2 : A = 2 * r := by omega
        have hedq : (e : ℚ) < d := by exact_mod_cast hexc h3
        have hDpos : (0 : ℚ) < (d : ℚ) + e := by
          have : (0 : ℤ) < d + e := by omega
          exact_mod_cast this
        have hβh : 2 * β < 1 := by
          have hβD : β * ((d : ℚ) + e) = e := hβ
          nlinarith only [hβD, hedq, hDpos, hβ0]
        have h3q : (e : ℚ) = 3 * r := by exact_mod_cast h3
        rw [hA2]; push_cast
        linarith only [R1, h3q, hβh, hκ0]
    exact_mod_cast h
  have G3 : 0 ≤ (e + r) * (z.1 - e) + (e - r) * (z.2 - r) := by
    have h : ((0 : ℤ) : ℚ) ≤ (((e + r) * (z.1 - e) + (e - r) * (z.2 - r) : ℤ) : ℚ) := by
      push_cast; rw [hs']; linarith only [htestq, hrq]
    exact_mod_cast h
  have G4 : (e + r) * (z.1 - e) + (e - r) * (z.2 - r) < 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r + 1 := by
    have h : (((e + r) * (z.1 - e) + (e - r) * (z.2 - r) : ℤ) : ℚ) <
        ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r + 1 : ℤ) : ℚ) := by
      push_cast; rw [hs']; linarith only [R4, hs, hκ0, hrq]
    exact_mod_cast h
  refine ⟨by linarith only [G1], by linarith only [G2], by linarith only [G3], by linarith only [G4]⟩

/-- `e = 3r` forces `e < d` in the W0 case. -/
theorem hexc_W0' (d n e r : ℤ) (hn : 0 < n) (hr : 0 < r) (hdet : d * r - n * e = 1) : e = 3 * r → e < d := by
  intro h
  subst h
  have h1 : r * (d - 3 * n) = 1 := by linarith
  have hpos : 0 < d - 3 * n := by
    by_contra hc
    push Not at hc
    nlinarith
  have h2 : 1 ≤ d - 3 * n := by omega
  have h3 : r * 1 ≤ r * (d - 3 * n) := mul_le_mul_of_nonneg_left h2 hr.le
  have h4 : r = 1 := by linarith
  omega

/-- **The `Q0` box cover (W0).** For a point `w` with cell coordinates `(u, v) ∈ [0, β]²`: `Q@0` or `Q@Q` contains it. -/
theorem Q0_cover (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = 1) (_hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (w : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (w.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (w.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hv0 : 0 ≤ v) (hv1 : v ≤ β) :
    InH ⟨r, e⟩ w ∨ InH ⟨r, e⟩ (w.1 - e, w.2 - r) := by
  rcases Int.emod_two_eq_zero_or_one (w.1 + w.2) with hpar | hpar
  · have hexc := hexc_W0' d n e r hn hr hdet
    obtain ⟨A, hA⟩ : ∃ A : ℤ, A = min (2 * r) (e - r) := ⟨_, rfl⟩
    by_cases htest : (e + r) * w.1 + (e - r) * w.2 ≤ e ^ 2 + 2 * e * r - r ^ 2 + 2 * r
    · exact Or.inl (inH_Q0_even_copy1 d n e r hn hnd hr hre hdet heven hexc w α β κ u v hz1 hz2 hα hβ hκ
        hu0 hu1 hv0 hv1 hpar A hA htest)
    · push Not at htest
      exact Or.inr (inH_Q0_even_copy2 d n e r hn hnd hr hre hdet heven hexc w α β κ u v hz1 hz2 hα hβ hκ
        hu0 hu1 hv0 hv1 hpar A hA htest)
  · obtain ⟨L, hL⟩ : ∃ L : ℤ, L = min (e - r) (3 * r - e) := ⟨_, rfl⟩
    by_cases htest : (e + r) * w.1 + (e - r) * w.2 ≤ e ^ 2 + 2 * e * r - r ^ 2 + 2 * r - L
    · exact Or.inl (inH_Q0_odd_copy1 d n e r hn hnd hr hre hdet heven w α β κ u v hz1 hz2 hα hβ hκ
        hu0 hu1 hv0 hv1 hpar L hL htest)
    · push Not at htest
      exact Or.inr (inH_Q0_odd_copy2 d n e r hn hnd hr hre hdet heven w α β κ u v hz1 hz2 hα hβ hκ
        hu0 hu1 hv0 hv1 hpar L hL htest)

end FLatticePaper.Tiles.PairW0Q
