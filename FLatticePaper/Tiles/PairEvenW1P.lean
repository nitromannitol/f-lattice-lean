import FLatticePaper.Tiles.PairW0P
import FLatticePaper.Tiles.EvenIneq

/-! Task 53, item 2 (covering reduction), section 13 (continued): the even child `X = 2P + Q` at flag true (`δ = dr − ne = −1`).

The `P`-window coordinates at a site `z` are `t = (d+n)/2 + u − G v` and `s = n + G u − 2v` (`δ = −1`), with `G = 2T_P + K`,
`T_P = d² + 2dn − n²`, `K = s_P(Q) = (d+n)e + (d−n)r`, and `Gα D = 2 T_P D − 2(d − n)`, `G e = D K + 2(d − n)`.

* `T3L`: the box `[0, α] × [0, α/2]` is owned by `P` at `0`.
* `T3H`: the box `[0, α] × [α/2, α]` is owned by `P` at `V_P = (n−d, n+d)`; the odd lower `s` facet uses `l ≤ n − 1`, i.e. `d ≠ 2n`. -/

namespace FLatticePaper.Tiles.PairEvenW1P

open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.PairW0P FLatticePaper.Tiles.EvenIneq

/-- The window of `P = (d, n)` has `μ = 2` (since `d + n` is odd). -/
theorem muP_two' (d n : ℤ) (hodd : (d + n) % 2 = 1) : muOf ⟨n, d⟩ = 2 := by
  show (if (n + d) % 2 = 1 then 2 else 1) = 2
  rw [if_pos (by omega)]

/-- **The box `[0, α] × [0, α/2]` of the flag-true even child is owned by `P` at `0`.** -/
theorem T3L_box (d n e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v α : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ))
    (hu0 : 0 ≤ u) (hu1 : u ≤ α) (hv0 : 0 ≤ v) (hv1 : 2 * v ≤ α) :
    InH ⟨n, d⟩ z := by
  have hdetQ : (d : ℚ) * r - n * e = -1 := by exact_mod_cast hdet
  have hDi : (0 : ℤ) < 2 * d + e := by omega
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by exact_mod_cast hDi
  have hmu : muOf ⟨n, d⟩ = 2 := muP_two' d n hodd
  have hc : (0 : ℚ) < (d : ℚ) - n := by exact_mod_cast (show (0 : ℤ) < d - n by omega)
  have heQ : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℤ) < e by omega)
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (show (0 : ℤ) < n by omega)
  have hrQ : (0 : ℚ) < r := by exact_mod_cast (show (0 : ℤ) < r by omega)
  have hdnpos : (0 : ℚ) < (d : ℚ) + n := by linarith only [hnQ, hc]
  obtain ⟨TP, hTP⟩ : ∃ T : ℚ, T = (d : ℚ) ^ 2 + 2 * d * n - (n : ℚ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℚ, K = ((d : ℚ) + n) * e + ((d : ℚ) - n) * r := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℚ, G = 2 * TP + K := ⟨_, rfl⟩
  have hTP0 : 0 < TP := by
    have h1 : (0 : ℚ) < ((d : ℚ) - n) * ((d : ℚ) + n) := mul_pos hc hdnpos
    have h2 : (0 : ℚ) < (d : ℚ) * n := mul_pos (by linarith only [hc, hnQ]) hnQ
    rw [hTP]
    linarith only [h1, h2]
  have hK0 : 0 < K := by
    have h1 : (0 : ℚ) < ((d : ℚ) + n) * e := mul_pos hdnpos heQ
    have h2 : (0 : ℚ) < ((d : ℚ) - n) * r := mul_pos hc hrQ
    rw [hK]
    linarith only [h1, h2]
  have hG0 : 0 ≤ G := by rw [hG]; linarith only [hTP0, hK0]
  -- the window coordinates of `z`
  have htz : (n : ℚ) * z.1 - d * z.2 = ((d : ℚ) + n) / 2 + u - G * v := by
    rw [hG, hTP, hK]
    linear_combination (n : ℚ) * hz1 - (d : ℚ) * hz2 + (-u) * hdetQ
  have hsz : ((d : ℚ) + n) * z.1 + ((d : ℚ) - n) * z.2 = n + G * u - 2 * v := by
    rw [hG, hTP, hK]
    linear_combination ((d : ℚ) + n) * hz1 + ((d : ℚ) - n) * hz2 + (2 * v) * hdetQ
  have hGαD : G * α * (2 * (d : ℚ) + e) = 2 * TP * (2 * (d : ℚ) + e) - 2 * ((d : ℚ) - n) := by
    rw [hG, hTP, hK]
    linear_combination (2 * ((d : ℚ) ^ 2 + 2 * d * n - (n : ℚ) ^ 2) + ((d : ℚ) + n) * e + ((d : ℚ) - n) * r) * hα
      + (2 * ((d : ℚ) - n)) * hdetQ
  have hGα_le : G * α ≤ 2 * TP := by
    apply le_of_mul_le_mul_right _ hD
    have e1 : (2 * TP) * (2 * (d : ℚ) + e) = 2 * TP * (2 * (d : ℚ) + e) := rfl
    rw [hGαD, e1]
    linarith only [hc]
  have hα1 : α < 1 := by
    apply lt_of_mul_lt_mul_right _ hD.le
    rw [hα]; linarith only [heQ]
  have hαpos : 0 < α := by
    apply pos_of_mul_pos_left _ hD.le
    rw [hα]; exact mul_pos (by norm_num) (by linarith only [hc, hnQ])
  -- real bounds
  have hGv : 2 * (G * v) ≤ G * α := by
    have := mul_le_mul_of_nonneg_left hv1 hG0
    linarith only [this]
  have hGu : G * u ≤ G * α := mul_le_mul_of_nonneg_left hu1 hG0
  have hGu0 : 0 ≤ G * u := mul_nonneg hG0 hu0
  have hGv0 : 0 ≤ G * v := mul_nonneg hG0 hv0
  have hlo_t : ((d : ℚ) + n) / 2 - TP ≤ n * z.1 - d * z.2 := by
    rw [htz]; linarith only [hGv, hGα_le, hu0]
  have hhi_t : n * z.1 - d * z.2 ≤ ((d : ℚ) + n) / 2 + α := by
    rw [htz]; linarith only [hGv0, hu1]
  have hlo_s : n - α ≤ ((d : ℚ) + n) * z.1 + ((d : ℚ) - n) * z.2 := by
    rw [hsz]; linarith only [hGu0, hv1]
  have hhi_s : ((d : ℚ) + n) * z.1 + ((d : ℚ) - n) * z.2 ≤ n + 2 * TP := by
    rw [hsz]; linarith only [hGu, hGα_le, hv0, hG]
  have hα_q : (0 : ℚ) < α := hαpos
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = min (2 * n) (d - n) := ⟨_, rfl⟩
  have ha2 : a ≤ 2 * n := by rw [ha]; exact min_le_left _ _
  have ha3 : a ≤ d - n := by rw [ha]; exact min_le_right _ _
  have hacase : a = 2 * n ∨ a = d - n := by rw [ha]; exact min_choice _ _
  have h2a : 2 * a + 1 ≤ d + n := by omega
  have ha_q : 2 * (a : ℚ) + 1 ≤ (d : ℚ) + n := by exact_mod_cast h2a
  have hd1 : (1 : ℚ) ≤ (d : ℚ) - n := by exact_mod_cast (show (1 : ℤ) ≤ d - n by omega)
  rcases Int.emod_two_eq_zero_or_one (z.1 + z.2) with hpar | hpar
  · -- even sites: `a = min(2n, d − n)`, `l = 0`
    have hev : decide ((z.1 + z.2) % 2 = 0) = true := decide_eq_true hpar
    rw [inH_P_iff d n z true hev hmu]
    have hA : aOf ⟨n, d⟩ true = a := by rw [ha]; simp [aOf]
    have hl : lOf ⟨n, d⟩ true = 0 := by simp [lOf]
    rw [hA, hl]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h : ((a - (d ^ 2 + 2 * d * n - n ^ 2) - 1 : ℤ) : ℚ) < ((n * z.1 - d * z.2 : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hlo_t
        linarith only [hlo_t, ha_q]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have h : ((n * z.1 - d * z.2 : ℤ) : ℚ) < ((d + n - a + 1 : ℤ) : ℚ) := by
        push_cast
        linarith only [hhi_t, ha_q, hα1]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith
    · have h : ((-1 : ℤ) : ℚ) < (((d + n) * z.1 + (d - n) * z.2 : ℤ) : ℚ) := by
        push_cast
        linarith only [hlo_s, hα1, hnQ]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have h : (((d + n) * z.1 + (d - n) * z.2 : ℤ) : ℚ) < ((2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0 + 1 : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hhi_s
        linarith only [hhi_s, hnQ]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith
  · -- odd sites: `a = n`, `l = min(d − n, 3n − d)`
    obtain ⟨L, hL⟩ : ∃ L : ℤ, L = min (d - n) (3 * n - d) := ⟨_, rfl⟩
    have hL1 : L ≤ d - n := by rw [hL]; exact min_le_left _ _
    have hL2 : L ≤ 3 * n - d := by rw [hL]; exact min_le_right _ _
    have hLcase : L = d - n ∨ L = 3 * n - d := by rw [hL]; exact min_choice _ _
    have hLn : L ≤ n := by omega
    have hLq : (L : ℚ) ≤ n := by exact_mod_cast hLn
    have hpar' : ¬ ((z.1 + z.2) % 2 = 0) := by omega
    have hev : decide ((z.1 + z.2) % 2 = 0) = false := decide_eq_false hpar'
    rw [inH_P_iff d n z false hev hmu]
    have hA : aOf ⟨n, d⟩ false = n := by simp [aOf]
    have hl : lOf ⟨n, d⟩ false = L := by rw [hL]; simp [lOf]
    rw [hA, hl]
    have hdn : (n : ℚ) < d := by exact_mod_cast hnd
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h : ((n - (d ^ 2 + 2 * d * n - n ^ 2) - 1 : ℤ) : ℚ) < ((n * z.1 - d * z.2 : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hlo_t
        linarith only [hlo_t, hdn]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have h : ((n * z.1 - d * z.2 : ℤ) : ℚ) < ((d + n - n + 1 : ℤ) : ℚ) := by
        push_cast
        linarith only [hhi_t, hα1, hd1]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith
    · have h : (((L - 1) : ℤ) : ℚ) < (((d + n) * z.1 + (d - n) * z.2 : ℤ) : ℚ) := by
        push_cast
        linarith only [hlo_s, hα1, hLq]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have h : (((d + n) * z.1 + (d - n) * z.2 : ℤ) : ℚ) < ((2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - L + 1 : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hhi_s
        linarith only [hhi_s, hLq]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith

/-- `d ≠ 2n` for `d ≥ 3` on the flag-true side (`d r − n e = −1`). -/
theorem d_ne_two_n' (d n e r : ℤ) (hd : 3 ≤ d) (hdet : d * r - n * e = -1) : d ≠ 2 * n := by
  intro h
  subst h
  have h1 : n * (e - 2 * r) = 1 := by linear_combination (-1 : ℤ) * hdet
  have h2 : n = 1 := Int.eq_one_of_mul_eq_one_right (by omega) h1
  omega

/-- **The box `[0, α] × [α/2, α]` of the flag-true even child is owned by `P` at `V_P`.** -/
theorem T3H_box (d n e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hd : 3 ≤ d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v α : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ))
    (hu0 : 0 ≤ u) (hu1 : u ≤ α) (hv0 : α ≤ 2 * v) (hv1 : v ≤ α) :
    InH ⟨n, d⟩ (z.1 - (n - d), z.2 - (n + d)) := by
  have hdetQ : (d : ℚ) * r - n * e = -1 := by exact_mod_cast hdet
  have hDi : (0 : ℤ) < 2 * d + e := by omega
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by exact_mod_cast hDi
  have hmu : muOf ⟨n, d⟩ = 2 := muP_two' d n hodd
  have hd2 : d ≠ 2 * n := d_ne_two_n' d n e r hd hdet
  have hc : (0 : ℚ) < (d : ℚ) - n := by exact_mod_cast (show (0 : ℤ) < d - n by omega)
  have heQ : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℤ) < e by omega)
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (show (0 : ℤ) < n by omega)
  have hrQ : (0 : ℚ) < r := by exact_mod_cast (show (0 : ℤ) < r by omega)
  have hn1 : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hdnpos : (0 : ℚ) < (d : ℚ) + n := by linarith only [hnQ, hc]
  have hcD : 2 * ((d : ℚ) - n) < 2 * (d : ℚ) + e := by linarith only [heQ, hnQ]
  have hd1 : (1 : ℚ) ≤ (d : ℚ) - n := by exact_mod_cast (show (1 : ℤ) ≤ d - n by omega)
  obtain ⟨TP, hTP⟩ : ∃ T : ℚ, T = (d : ℚ) ^ 2 + 2 * d * n - (n : ℚ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℚ, K = ((d : ℚ) + n) * e + ((d : ℚ) - n) * r := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℚ, G = 2 * TP + K := ⟨_, rfl⟩
  have hTP0 : 0 < TP := by
    have h1 : (0 : ℚ) < ((d : ℚ) - n) * ((d : ℚ) + n) := mul_pos hc hdnpos
    have h2 : (0 : ℚ) < (d : ℚ) * n := mul_pos (by linarith only [hc, hnQ]) hnQ
    rw [hTP]
    linarith only [h1, h2]
  have hK0 : 0 < K := by
    have h1 : (0 : ℚ) < ((d : ℚ) + n) * e := mul_pos hdnpos heQ
    have h2 : (0 : ℚ) < ((d : ℚ) - n) * r := mul_pos hc hrQ
    rw [hK]
    linarith only [h1, h2]
  have hG0 : 0 ≤ G := by rw [hG]; linarith only [hTP0, hK0]
  -- the window coordinates of `z − V_P`
  have htw : (n : ℚ) * (z.1 - (n - d)) - d * (z.2 - (n + d)) = ((d : ℚ) + n) / 2 + u - G * v + TP := by
    rw [hG, hTP, hK]
    linear_combination (n : ℚ) * hz1 - (d : ℚ) * hz2 + (-u) * hdetQ
  have hsw : ((d : ℚ) + n) * (z.1 - (n - d)) + ((d : ℚ) - n) * (z.2 - (n + d)) = n + G * u - 2 * v := by
    rw [hG, hTP, hK]
    linear_combination ((d : ℚ) + n) * hz1 + ((d : ℚ) - n) * hz2 + (2 * v) * hdetQ
  have hGαD : G * α * (2 * (d : ℚ) + e) = 2 * TP * (2 * (d : ℚ) + e) - 2 * ((d : ℚ) - n) := by
    rw [hG, hTP, hK]
    linear_combination (2 * ((d : ℚ) ^ 2 + 2 * d * n - (n : ℚ) ^ 2) + ((d : ℚ) + n) * e + ((d : ℚ) - n) * r) * hα
      + (2 * ((d : ℚ) - n)) * hdetQ
  have hα1 : α < 1 := by
    apply lt_of_mul_lt_mul_right _ hD.le
    rw [hα]; linarith only [heQ]
  have hαpos : 0 < α := by
    apply pos_of_mul_pos_left _ hD.le
    rw [hα]; linarith only [hc, hnQ]
  have hGα_le : G * α ≤ 2 * TP := by
    apply le_of_mul_le_mul_right _ hD
    rw [hGαD]
    linarith only [hc]
  have hGα_ge : 2 * TP - 1 ≤ G * α := by
    apply le_of_mul_le_mul_right _ hD
    have e1 : (2 * TP - 1) * (2 * (d : ℚ) + e) = 2 * TP * (2 * (d : ℚ) + e) - (2 * (d : ℚ) + e) := by ring
    rw [hGαD, e1]
    linarith only [hcD]
  have hGv_hi : G * v ≤ G * α := mul_le_mul_of_nonneg_left hv1 hG0
  have hGv_lo : G * α ≤ 2 * (G * v) := by
    have := mul_le_mul_of_nonneg_left hv0 hG0
    linarith only [this]
  have hGu : G * u ≤ G * α := mul_le_mul_of_nonneg_left hu1 hG0
  have hGu0 : 0 ≤ G * u := mul_nonneg hG0 hu0
  have hv_nn : 0 ≤ v := by linarith only [hv0, hαpos]
  have hGv0 : 0 ≤ G * v := mul_nonneg hG0 hv_nn
  -- real bounds of the window coordinates
  have hlo_t : ((d : ℚ) + n) / 2 - TP ≤ n * (z.1 - (n - d)) - d * (z.2 - (n + d)) := by
    rw [htw]; linarith only [hGv_hi, hGα_le, hu0]
  have hhi_t : n * (z.1 - (n - d)) - d * (z.2 - (n + d)) ≤ ((d : ℚ) + n) / 2 + α + 1 / 2 := by
    rw [htw]; linarith only [hGv_lo, hGα_ge, hu1]
  have hlo_s : n - 2 * α ≤ ((d : ℚ) + n) * (z.1 - (n - d)) + ((d : ℚ) - n) * (z.2 - (n + d)) := by
    rw [hsw]; linarith only [hGu0, hv1]
  have hhi_s : ((d : ℚ) + n) * (z.1 - (n - d)) + ((d : ℚ) - n) * (z.2 - (n + d)) ≤ n + 2 * TP := by
    rw [hsw]; linarith only [hGu, hGα_le, hv_nn]
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = min (2 * n) (d - n) := ⟨_, rfl⟩
  have ha2 : a ≤ 2 * n := by rw [ha]; exact min_le_left _ _
  have ha3 : a ≤ d - n := by rw [ha]; exact min_le_right _ _
  have hacase : a = 2 * n ∨ a = d - n := by rw [ha]; exact min_choice _ _
  have h2a : 2 * a + 1 ≤ d + n := by omega
  have ha_q : 2 * (a : ℚ) + 1 ≤ (d : ℚ) + n := by exact_mod_cast h2a
  rcases Int.emod_two_eq_zero_or_one ((z.1 - (n - d)) + (z.2 - (n + d))) with hpar | hpar
  · -- even `w`: `a = min(2n, d − n)`, `l = 0`
    have hev : decide ((((z.1 - (n - d), z.2 - (n + d)) : ℤ × ℤ).1 + (z.1 - (n - d), z.2 - (n + d)).2) % 2 = 0) = true :=
      decide_eq_true hpar
    rw [inH_P_iff d n (z.1 - (n - d), z.2 - (n + d)) true hev hmu]
    have hA : aOf ⟨n, d⟩ true = a := by rw [ha]; simp [aOf]
    have hl : lOf ⟨n, d⟩ true = 0 := by simp [lOf]
    rw [hA, hl]
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h : ((a - (d ^ 2 + 2 * d * n - n ^ 2) - 1 : ℤ) : ℚ) < ((n * (z.1 - (n - d)) - d * (z.2 - (n + d)) : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hlo_t
        linarith only [hlo_t, ha_q]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have h : ((n * (z.1 - (n - d)) - d * (z.2 - (n + d)) : ℤ) : ℚ) < ((d + n - a + 1 : ℤ) : ℚ) := by
        push_cast
        linarith only [hhi_t, ha_q, hα1]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith
    · have h : ((-1 : ℤ) : ℚ) < (((d + n) * (z.1 - (n - d)) + (d - n) * (z.2 - (n + d)) : ℤ) : ℚ) := by
        push_cast
        linarith only [hlo_s, hα1, hn1]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have h : (((d + n) * (z.1 - (n - d)) + (d - n) * (z.2 - (n + d)) : ℤ) : ℚ) <
          ((2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0 + 1 : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hhi_s
        linarith only [hhi_s, hnQ]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith
  · -- odd `w`: `a = n`, `l = min(d − n, 3n − d)`
    obtain ⟨L, hL⟩ : ∃ L : ℤ, L = min (d - n) (3 * n - d) := ⟨_, rfl⟩
    have hL1 : L ≤ d - n := by rw [hL]; exact min_le_left _ _
    have hL2 : L ≤ 3 * n - d := by rw [hL]; exact min_le_right _ _
    have hLcase : L = d - n ∨ L = 3 * n - d := by rw [hL]; exact min_choice _ _
    have hLn : L ≤ n - 1 := by omega
    have hLq : (L : ℚ) ≤ n - 1 := by exact_mod_cast hLn
    have hpar' : ¬ (((z.1 - (n - d)) + (z.2 - (n + d))) % 2 = 0) := by omega
    have hev : decide ((((z.1 - (n - d), z.2 - (n + d)) : ℤ × ℤ).1 + (z.1 - (n - d), z.2 - (n + d)).2) % 2 = 0) = false :=
      decide_eq_false hpar'
    rw [inH_P_iff d n (z.1 - (n - d), z.2 - (n + d)) false hev hmu]
    have hA : aOf ⟨n, d⟩ false = n := by simp [aOf]
    have hl : lOf ⟨n, d⟩ false = L := by rw [hL]; simp [lOf]
    rw [hA, hl]
    dsimp only
    have hdn : (n : ℚ) < d := by exact_mod_cast hnd
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h : ((n - (d ^ 2 + 2 * d * n - n ^ 2) - 1 : ℤ) : ℚ) < ((n * (z.1 - (n - d)) - d * (z.2 - (n + d)) : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hlo_t
        linarith only [hlo_t, hdn]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have h : ((n * (z.1 - (n - d)) - d * (z.2 - (n + d)) : ℤ) : ℚ) < ((d + 1 : ℤ) : ℚ) := by
        push_cast
        linarith only [hhi_t, hα1, hd1]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith
    · have h : (((L - 1) : ℤ) : ℚ) < (((d + n) * (z.1 - (n - d)) + (d - n) * (z.2 - (n + d)) : ℤ) : ℚ) := by
        push_cast
        linarith only [hlo_s, hα1, hLq]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have h : (((d + n) * (z.1 - (n - d)) + (d - n) * (z.2 - (n + d)) : ℤ) : ℚ) <
          ((2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - L + 1 : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hhi_s
        linarith only [hhi_s, hLq, hn1]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith

end FLatticePaper.Tiles.PairEvenW1P
