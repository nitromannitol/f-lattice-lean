import FLatticePaper.Tiles.PairW0P
import FLatticePaper.Tiles.EvenIneq

/-! Task 53, item 2 (covering reduction), section 13 (continued): the even child `X = 2P + Q` at flag false (`δ = +1`).

Box `[β, 1] × [0, α/2]` is owned by the source `P` at `Q`: for every integer `z` of the box, `z − Q ∈ H_P`.
With `T_P = d² + 2dn − n²`, `K = s_P(Q) = (d+n)e + (d−n)r`, `G = 2T_P + K`, the `P`-window coordinates of `z − Q` are
`t = (d+n)/2 + 1 − u − G v` and `s = n − K + G u + 2v` (the determinant is `+1`).
The integer parts: `a = min(2n, d−n)` (even), `a = n` (odd); `l = 0` (even), `l = min(d−n, 3n−d)` (odd).
Key identity: `D (n − K + Gβ − L + 1) = D (n + 1 − L) − 2(d − n)` with `L = l`, from `G e − D K = −2(d − n)`. -/

namespace FLatticePaper.Tiles.PairEvenW0P

open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.PairW0P FLatticePaper.Tiles.EvenIneq

/-- The window of `P = (d, n)` has `μ = 2` (since `d + n` is odd). -/
theorem muP_two (d n : ℤ) (hodd : (d + n) % 2 = 1) : muOf ⟨n, d⟩ = 2 := by
  show (if (n + d) % 2 = 1 then 2 else 1) = 2
  rw [if_pos (by omega)]

/-- **The box `[β, 1] × [0, α/2]` of the flag-false even child is owned by `P` at `Q`.** -/
theorem F3L_box (d n e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v α β : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ))
    (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hu0 : β ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : 2 * v ≤ α) :
    InH ⟨n, d⟩ (z.1 - e, z.2 - r) := by
  have hdetQ : (d : ℚ) * r - n * e = 1 := by exact_mod_cast hdet
  have hDi : (0 : ℤ) < 2 * d + e := by omega
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by exact_mod_cast hDi
  have hmu : muOf ⟨n, d⟩ = 2 := muP_two d n hodd
  have hc : (0 : ℚ) < (d : ℚ) - n := by exact_mod_cast (show (0 : ℤ) < d - n by omega)
  have heQ : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℤ) < e by omega)
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (show (0 : ℤ) < n by omega)
  have hcD : 2 * ((d : ℚ) - n) < 2 * (d : ℚ) + e := by linarith
  obtain ⟨TP, hTP⟩ : ∃ T : ℚ, T = (d : ℚ) ^ 2 + 2 * d * n - (n : ℚ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℚ, K = ((d : ℚ) + n) * e + ((d : ℚ) - n) * r := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℚ, G = 2 * TP + K := ⟨_, rfl⟩
  have hTP0 : 0 < TP := by
    rw [hTP]
    have : (0 : ℚ) < d - n := hc
    have hn' : (1 : ℚ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hK0 : 0 < K := by
    rw [hK]
    have h1 : (0 : ℚ) < (d : ℚ) + n := by exact_mod_cast (show (0 : ℤ) < d + n by omega)
    have h3 : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℤ) < e by omega)
    have h4 : (0 : ℚ) < r := by exact_mod_cast (show (0 : ℤ) < r by omega)
    nlinarith [mul_pos h1 h3, mul_pos hc h4]
  have hG0 : 0 ≤ G := by rw [hG]; linarith
  -- the window coordinates of `z − Q`
  have htw : (n : ℚ) * (z.1 - e) - d * (z.2 - r) = ((d : ℚ) + n) / 2 + 1 - u - G * v := by
    rw [hG, hTP, hK]
    linear_combination (n : ℚ) * hz1 - (d : ℚ) * hz2 + (1 - u) * hdetQ
  have hsw : ((d : ℚ) + n) * (z.1 - e) + ((d : ℚ) - n) * (z.2 - r) = n - K + G * u + 2 * v := by
    rw [hG, hTP, hK]
    linear_combination ((d : ℚ) + n) * hz1 + ((d : ℚ) - n) * hz2 + (2 * v) * hdetQ
  -- `G α ≤ 2 T_P + 2` and `G β` identities
  have hGαD : G * α * (2 * (d : ℚ) + e) = 2 * TP * (2 * (d : ℚ) + e) + 2 * ((d : ℚ) - n) := by
    rw [hG, hTP, hK]
    linear_combination (2 * ((d : ℚ) ^ 2 + 2 * d * n - (n : ℚ) ^ 2) + ((d : ℚ) + n) * e + ((d : ℚ) - n) * r) * hα
      + (2 * ((d : ℚ) - n)) * hdetQ
  have hGα : G * α ≤ 2 * TP + 2 := by
    apply le_of_mul_le_mul_right _ hD
    have e1 : (2 * TP + 2) * (2 * (d : ℚ) + e) = 2 * TP * (2 * (d : ℚ) + e) + 2 * (2 * (d : ℚ) + e) := by ring
    rw [hGαD, e1]
    linarith
  have hGe : G * e = (2 * (d : ℚ) + e) * K - 2 * ((d : ℚ) - n) := by
    rw [hG, hTP, hK]
    linear_combination (-2 * ((d : ℚ) - n)) * hdetQ
  have hGβD : G * β * (2 * (d : ℚ) + e) = G * e := by linear_combination G * hβ
  have hβ0 : 0 < β := by
    apply pos_of_mul_pos_left _ hD.le
    rw [hβ]
    exact_mod_cast (show (0 : ℤ) < e by omega)
  have hα2 : α < 2 := by
    apply lt_of_mul_lt_mul_right _ hD.le
    rw [hα]; linarith
  -- the real bounds of `t` and `s`
  have hGv : 2 * (G * v) ≤ G * α := by
    have := mul_le_mul_of_nonneg_left hv1 hG0
    linarith
  have hGv0 : 0 ≤ G * v := mul_nonneg hG0 hv0
  have hGuβ : G * β ≤ G * u := mul_le_mul_of_nonneg_left hu0 hG0
  have hGu1 : G * u ≤ G := by
    have := mul_le_mul_of_nonneg_left hu1 hG0
    linarith
  have hGu0 : 0 ≤ G * u := mul_nonneg hG0 (by linarith)
  -- real facets of the window
  have hlo_real : ((d : ℚ) + n) / 2 - TP - 1 ≤ n * (z.1 - e) - d * (z.2 - r) := by
    rw [htw]; linarith [hGv, hGα, hu1]
  have hup_real : n * (z.1 - e) - d * (z.2 - r) ≤ ((d : ℚ) + n) / 2 + 1 - β := by
    rw [htw]; linarith [hGv0, hu0]
  have hsw_lo : n - K + G * β ≤ ((d : ℚ) + n) * (z.1 - e) + ((d : ℚ) - n) * (z.2 - r) := by
    rw [hsw]; linarith [hGuβ, hv0]
  have hsw_hi : ((d : ℚ) + n) * (z.1 - e) + ((d : ℚ) - n) * (z.2 - r) ≤ n + 2 * TP + α := by
    rw [hsw]; linarith [hGu1, hv1, hG]
  -- positivity of `n − K + G β − (L − 1)` for every integer `L ≤ n`
  have hX : ∀ L : ℤ, L ≤ n → 0 < (n : ℚ) - K + G * β - ((L : ℚ) - 1) := by
    intro L hL
    have hLq : (L : ℚ) ≤ n := by exact_mod_cast hL
    have hidX : (2 * (d : ℚ) + e) * ((n : ℚ) - K + G * β - ((L : ℚ) - 1)) =
        (2 * (d : ℚ) + e) * ((n : ℚ) + 1 - L) - 2 * ((d : ℚ) - n) := by
      linear_combination hGβD + hGe
    have h1 : (2 * (d : ℚ) + e) * 1 ≤ (2 * (d : ℚ) + e) * ((n : ℚ) + 1 - L) :=
      mul_le_mul_of_nonneg_left (by linarith) hD.le
    apply lt_of_mul_lt_mul_left _ hD.le
    rw [mul_zero, hidX]
    linarith [hcD, h1]
  have hα1 : α < 2 := hα2
  -- even sites: `a = min(2n, d − n)` and `l = 0`
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = min (2 * n) (d - n) := ⟨_, rfl⟩
  have ha2 : a ≤ 2 * n := by rw [ha]; exact min_le_left _ _
  have ha3 : a ≤ d - n := by rw [ha]; exact min_le_right _ _
  have hacase : a = 2 * n ∨ a = d - n := by
    rw [ha]; exact min_choice _ _
  have h2a : 2 * a < d + n := by omega
  have ha_q : 2 * (a : ℚ) < (d : ℚ) + n := by exact_mod_cast h2a
  have hX0 : 0 < (n : ℚ) - K + G * β + 1 := by
    have := hX 0 (by omega)
    push_cast at this
    linarith
  rcases Int.emod_two_eq_zero_or_one (z.1 - e + (z.2 - r)) with hpar | hpar
  · -- even `w`: `a = min(2n, d−n)`, `l = 0`
    have hev : decide ((((z.1 - e, z.2 - r) : ℤ × ℤ).1 + (z.1 - e, z.2 - r).2) % 2 = 0) = true :=
      decide_eq_true hpar
    rw [inH_P_iff d n (z.1 - e, z.2 - r) true hev (muP_two d n hodd)]
    have hA : aOf ⟨n, d⟩ true = a := by rw [ha]; simp [aOf]
    have hl : lOf ⟨n, d⟩ true = 0 := by simp [lOf]
    rw [hA, hl]
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h : ((a - (d ^ 2 + 2 * d * n - n ^ 2) - 1 : ℤ) : ℚ) < ((n * (z.1 - e) - d * (z.2 - r) : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hlo_real
        linarith [hlo_real, ha_q]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have h : ((n * (z.1 - e) - d * (z.2 - r) : ℤ) : ℚ) < ((d + n - a + 1 : ℤ) : ℚ) := by
        push_cast
        have hb : (0 : ℚ) < β := hβ0
        linarith [hup_real, ha_q, hb]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith
    · have h : ((-1 : ℤ) : ℚ) < (((d + n) * (z.1 - e) + (d - n) * (z.2 - r) : ℤ) : ℚ) := by
        push_cast
        linarith [hsw_lo, hX0]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have hα' : α < n + 1 := by
        have : (1 : ℚ) ≤ n := by exact_mod_cast hn
        linarith [hα2]
      have h : (((d + n) * (z.1 - e) + (d - n) * (z.2 - r) : ℤ) : ℚ) < ((2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0 + 1 : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hsw_hi
        linarith [hsw_hi, hα', hTP]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith
  · -- odd `w`: `a = n`, `l = min(d − n, 3n − d)`
    obtain ⟨L, hL⟩ : ∃ L : ℤ, L = min (d - n) (3 * n - d) := ⟨_, rfl⟩
    have hL1 : L ≤ d - n := by rw [hL]; exact min_le_left _ _
    have hL2 : L ≤ 3 * n - d := by rw [hL]; exact min_le_right _ _
    have hLcase : L = d - n ∨ L = 3 * n - d := by rw [hL]; exact min_choice _ _
    have hLn : L ≤ n := by omega
    have hX' : 0 < (n : ℚ) - K + G * β - ((L : ℚ) - 1) := hX L hLn
    have hpar' : ¬ ((z.1 - e + (z.2 - r)) % 2 = 0) := by omega
    have hev : decide ((((z.1 - e, z.2 - r) : ℤ × ℤ).1 + (z.1 - e, z.2 - r).2) % 2 = 0) = false :=
      decide_eq_false hpar'
    rw [inH_P_iff d n (z.1 - e, z.2 - r) false hev (muP_two d n hodd)]
    have hA : aOf ⟨n, d⟩ false = n := by simp [aOf]
    have hl : lOf ⟨n, d⟩ false = L := by rw [hL]; simp [lOf]
    rw [hA, hl]
    dsimp only
    have hdn : (n : ℚ) < d := by exact_mod_cast hnd
    have hβ' : (0 : ℚ) < β := hβ0
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h : ((n - (d ^ 2 + 2 * d * n - n ^ 2) - 1 : ℤ) : ℚ) < ((n * (z.1 - e) - d * (z.2 - r) : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hlo_real
        linarith [hlo_real, hdn]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have h : ((n * (z.1 - e) - d * (z.2 - r) : ℤ) : ℚ) < ((d + 1 : ℤ) : ℚ) := by
        push_cast
        linarith [hup_real, hdn, hβ']
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith
    · have h : (((L - 1) : ℤ) : ℚ) < (((d + n) * (z.1 - e) + (d - n) * (z.2 - r) : ℤ) : ℚ) := by
        push_cast
        linarith [hsw_lo, hX']
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have hαL : α < (n : ℚ) - L + 1 := by
        rcases (show L = n ∨ L + 1 ≤ n by omega) with h1 | h1
        · rw [h1]
          have hαD : α * (2 * (d : ℚ) + e) < 1 * (2 * (d : ℚ) + e) := by
            rw [hα]; linarith
          have := lt_of_mul_lt_mul_right hαD hD.le
          linarith
        · have : (L : ℚ) + 1 ≤ n := by exact_mod_cast h1
          linarith [hα2]
      have h : (((d + n) * (z.1 - e) + (d - n) * (z.2 - r) : ℤ) : ℚ) <
          ((2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - L + 1 : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hsw_hi
        linarith [hsw_hi, hαL]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith


/-- `d ≠ 2n` for `d ≥ 3` (the determinant is a unit, so `n ∣ 1`). -/
theorem d_ne_two_n (d n e r : ℤ) (hd : 3 ≤ d) (hdet : d * r - n * e = 1) : d ≠ 2 * n := by
  intro h
  subst h
  have h1 : n * (2 * r - e) = 1 := by linear_combination hdet
  have h2 : n = 1 := Int.eq_one_of_mul_eq_one_right (by omega) h1
  omega

/-- **The box `[β, 1] × [α/2, α]` of the flag-false even child is owned by `P` at `Q + V_P`.** -/
theorem F3H_box (d n e r : ℤ) (hn : 1 ≤ n) (hnd : n < d) (hdn : d ≠ 2 * n ∨ 2 * d < e) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v α β : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ))
    (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hu0 : β ≤ u) (hu1 : u ≤ 1) (hv0 : α ≤ 2 * v) (hv1 : v ≤ α) :
    InH ⟨n, d⟩ (z.1 - (e + (n - d)), z.2 - (r + (n + d))) := by
  have hdetQ : (d : ℚ) * r - n * e = 1 := by exact_mod_cast hdet
  have hDi : (0 : ℤ) < 2 * d + e := by omega
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by exact_mod_cast hDi
  have hmu : muOf ⟨n, d⟩ = 2 := muP_two d n hodd
  have heQ : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℤ) < e by omega)
  have hnQ : (0 : ℚ) < n := by exact_mod_cast (show (0 : ℤ) < n by omega)
  have hc : (0 : ℚ) < (d : ℚ) - n := by exact_mod_cast (show (0 : ℤ) < d - n by omega)
  have hcD : 2 * ((d : ℚ) - n) < 2 * (d : ℚ) + e := by linarith
  obtain ⟨TP, hTP⟩ : ∃ T : ℚ, T = (d : ℚ) ^ 2 + 2 * d * n - (n : ℚ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℚ, K = ((d : ℚ) + n) * e + ((d : ℚ) - n) * r := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℚ, G = 2 * TP + K := ⟨_, rfl⟩
  have hrQ : (0 : ℚ) < r := by exact_mod_cast (show (0 : ℤ) < r by omega)
  have hdnpos : (0 : ℚ) < (d : ℚ) + n := by linarith only [hnQ, hc, heQ]
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
  -- the window coordinates of `z − (Q + V_P)`
  have htw : (n : ℚ) * (z.1 - (e + (n - d))) - d * (z.2 - (r + (n + d))) =
      ((d : ℚ) + n) / 2 + 1 - u - G * v + TP := by
    rw [hG, hTP, hK]
    linear_combination (n : ℚ) * hz1 - (d : ℚ) * hz2 + (1 - u) * hdetQ
  have hsw : ((d : ℚ) + n) * (z.1 - (e + (n - d))) + ((d : ℚ) - n) * (z.2 - (r + (n + d))) =
      n - K + G * u + 2 * v := by
    rw [hG, hTP, hK]
    linear_combination ((d : ℚ) + n) * hz1 + ((d : ℚ) - n) * hz2 + (2 * v) * hdetQ
  have hGαD : G * α * (2 * (d : ℚ) + e) = 2 * TP * (2 * (d : ℚ) + e) + 2 * ((d : ℚ) - n) := by
    rw [hG, hTP, hK]
    linear_combination (2 * ((d : ℚ) ^ 2 + 2 * d * n - (n : ℚ) ^ 2) + ((d : ℚ) + n) * e + ((d : ℚ) - n) * r) * hα
      + (2 * ((d : ℚ) - n)) * hdetQ
  have hGe : G * e = (2 * (d : ℚ) + e) * K - 2 * ((d : ℚ) - n) := by
    rw [hG, hTP, hK]
    linear_combination (-2 * ((d : ℚ) - n)) * hdetQ
  have hGβD : G * β * (2 * (d : ℚ) + e) = G * e := by linear_combination G * hβ
  have hβ0 : 0 < β := by
    apply pos_of_mul_pos_left _ hD.le
    rw [hβ]; exact heQ
  have hα2 : α < 1 := by
    apply lt_of_mul_lt_mul_right _ hD.le
    rw [hα]; linarith
  have hαpos : 0 ≤ α := by linarith [hv0, hv1]
  -- real bounds: `G α` is within `[2T_P, 2T_P + 1)`
  have hGα_lo : 2 * TP ≤ G * α := by
    apply le_of_mul_le_mul_right _ hD
    rw [hGαD]
    linarith only [hc]
  have hGα_hi : G * α < 2 * TP + 1 := by
    apply lt_of_mul_lt_mul_right _ hD.le
    have e1 : (2 * TP + 1) * (2 * (d : ℚ) + e) = 2 * TP * (2 * (d : ℚ) + e) + (2 * (d : ℚ) + e) := by ring
    rw [hGαD, e1]
    linarith
  have hGv : G * α ≤ 2 * (G * v) := by
    have := mul_le_mul_of_nonneg_left hv0 hG0
    linarith
  have hGv0 : 0 ≤ G * v := mul_nonneg hG0 (by linarith)
  have hGuβ : G * β ≤ G * u := mul_le_mul_of_nonneg_left hu0 hG0
  have hGu1 : G * u ≤ G := by
    have := mul_le_mul_of_nonneg_left hu1 hG0
    linarith
  have hv_nn : 0 ≤ v := by linarith
  -- real facets of the window
  have hGvα : G * v ≤ G * α := mul_le_mul_of_nonneg_left hv1 hG0
  have hlo_real : ((d : ℚ) + n) / 2 - TP - 1 < n * (z.1 - (e + (n - d))) - d * (z.2 - (r + (n + d))) := by
    rw [htw]; linarith only [hGα_hi, hGvα, hu1]
  have hup_real : n * (z.1 - (e + (n - d))) - d * (z.2 - (r + (n + d))) ≤ ((d : ℚ) + n) / 2 + 1 - β := by
    rw [htw]; linarith [hGα_lo, hGv, hu0]
  have hsw_lo : n - K + G * β ≤ ((d : ℚ) + n) * (z.1 - (e + (n - d))) + ((d : ℚ) - n) * (z.2 - (r + (n + d))) := by
    rw [hsw]; linarith [hGuβ, hv_nn]
  have hsw_hi : ((d : ℚ) + n) * (z.1 - (e + (n - d))) + ((d : ℚ) - n) * (z.2 - (r + (n + d))) ≤ n + 2 * TP + 2 * α := by
    rw [hsw]; linarith only [hGu1, hv1, hG]
  -- positivity of `n − K + G β − (L − 1)` for `L ≤ n`
  have hX : ∀ L : ℤ, L ≤ n → 0 < (n : ℚ) - K + G * β - ((L : ℚ) - 1) := by
    intro L hL
    have hLq : (L : ℚ) ≤ n := by exact_mod_cast hL
    have hidX : (2 * (d : ℚ) + e) * ((n : ℚ) - K + G * β - ((L : ℚ) - 1)) =
        (2 * (d : ℚ) + e) * ((n : ℚ) + 1 - L) - 2 * ((d : ℚ) - n) := by
      linear_combination hGβD + hGe
    have h1 : (2 * (d : ℚ) + e) * 1 ≤ (2 * (d : ℚ) + e) * ((n : ℚ) + 1 - L) :=
      mul_le_mul_of_nonneg_left (by linarith) hD.le
    apply lt_of_mul_lt_mul_left _ hD.le
    rw [mul_zero, hidX]
    linarith [hcD, h1]
  -- even sites: `a = min(2n, d − n)` and `l = 0`
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = min (2 * n) (d - n) := ⟨_, rfl⟩
  have ha2 : a ≤ 2 * n := by rw [ha]; exact min_le_left _ _
  have ha3 : a ≤ d - n := by rw [ha]; exact min_le_right _ _
  have hacase : a = 2 * n ∨ a = d - n := by
    rw [ha]; exact min_choice _ _
  have h2a : 2 * a < d + n := by omega
  have ha_q : 2 * (a : ℚ) < (d : ℚ) + n := by exact_mod_cast h2a
  have hX0 : 0 < (n : ℚ) - K + G * β + 1 := by
    have := hX 0 (by omega)
    push_cast at this
    linarith
  rcases Int.emod_two_eq_zero_or_one (z.1 - (e + (n - d)) + (z.2 - (r + (n + d)))) with hpar | hpar
  · -- even `w`: `a = min(2n, d−n)`, `l = 0`
    have hev : decide ((((z.1 - (e + (n - d)), z.2 - (r + (n + d))) : ℤ × ℤ).1 +
        (z.1 - (e + (n - d)), z.2 - (r + (n + d))).2) % 2 = 0) = true := decide_eq_true hpar
    rw [inH_P_iff d n (z.1 - (e + (n - d)), z.2 - (r + (n + d))) true hev hmu]
    have hA : aOf ⟨n, d⟩ true = a := by rw [ha]; simp [aOf]
    have hl : lOf ⟨n, d⟩ true = 0 := by simp [lOf]
    rw [hA, hl]
    dsimp only
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h : ((a - (d ^ 2 + 2 * d * n - n ^ 2) - 1 : ℤ) : ℚ) < ((n * (z.1 - (e + (n - d))) - d * (z.2 - (r + (n + d))) : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hlo_real
        linarith [hlo_real, ha_q]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have h : ((n * (z.1 - (e + (n - d))) - d * (z.2 - (r + (n + d))) : ℤ) : ℚ) < ((d + n - a + 1 : ℤ) : ℚ) := by
        push_cast
        linarith [hup_real, ha_q, hβ0]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith
    · have h : ((-1 : ℤ) : ℚ) < (((d + n) * (z.1 - (e + (n - d))) + (d - n) * (z.2 - (r + (n + d))) : ℤ) : ℚ) := by
        push_cast
        linarith [hsw_lo, hX0]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have h : (((d + n) * (z.1 - (e + (n - d))) + (d - n) * (z.2 - (r + (n + d))) : ℤ) : ℚ) <
          ((2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0 + 1 : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hsw_hi
        have : (1 : ℚ) ≤ n := by exact_mod_cast hn
        linarith [hsw_hi, hα2]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith
  · -- odd `w`: `a = n`, `l = min(d − n, 3n − d)`
    obtain ⟨L, hL⟩ : ∃ L : ℤ, L = min (d - n) (3 * n - d) := ⟨_, rfl⟩
    have hL1 : L ≤ d - n := by rw [hL]; exact min_le_left _ _
    have hL2 : L ≤ 3 * n - d := by rw [hL]; exact min_le_right _ _
    have hLcase : L = d - n ∨ L = 3 * n - d := by rw [hL]; exact min_choice _ _
    have hLn : L ≤ n := by omega
    have hX' : 0 < (n : ℚ) - K + G * β - ((L : ℚ) - 1) := hX L hLn
    have hpar' : ¬ ((z.1 - (e + (n - d)) + (z.2 - (r + (n + d)))) % 2 = 0) := by omega
    have hev : decide ((((z.1 - (e + (n - d)), z.2 - (r + (n + d))) : ℤ × ℤ).1 +
        (z.1 - (e + (n - d)), z.2 - (r + (n + d))).2) % 2 = 0) = false := decide_eq_false hpar'
    rw [inH_P_iff d n (z.1 - (e + (n - d)), z.2 - (r + (n + d))) false hev hmu]
    have hA : aOf ⟨n, d⟩ false = n := by simp [aOf]
    have hl : lOf ⟨n, d⟩ false = L := by rw [hL]; simp [lOf]
    rw [hA, hl]
    dsimp only
    have hndQ : (n : ℚ) < d := by exact_mod_cast hnd
    have hβ' : (0 : ℚ) < β := hβ0
    refine ⟨?_, ?_, ?_, ?_⟩
    · have h : ((n - (d ^ 2 + 2 * d * n - n ^ 2) - 1 : ℤ) : ℚ) < ((n * (z.1 - (e + (n - d))) - d * (z.2 - (r + (n + d))) : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hlo_real
        linarith [hlo_real, hndQ]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have h : ((n * (z.1 - (e + (n - d))) - d * (z.2 - (r + (n + d))) : ℤ) : ℚ) < ((d + 1 : ℤ) : ℚ) := by
        push_cast
        linarith [hup_real, hndQ, hβ']
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith
    · have h : (((L - 1) : ℤ) : ℚ) < (((d + n) * (z.1 - (e + (n - d))) + (d - n) * (z.2 - (r + (n + d))) : ℤ) : ℚ) := by
        push_cast
        linarith [hsw_lo, hX']
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · have hαL : 2 * α < (n : ℚ) - L + 1 := by
        rcases (show L + 1 ≤ n ∨ L = n by omega) with h1 | h1
        · have : (L : ℚ) + 1 ≤ n := by exact_mod_cast h1
          linarith [hα2]
        · have hdn2 : 2 * d < e := hdn.resolve_left (fun h => h (by omega))
          have h2d : (2 : ℚ) * d < e := by exact_mod_cast hdn2
          have e2 : 2 * α * (2 * (d : ℚ) + e) = 4 * d := by linear_combination 2 * hα
          have hα1 : 2 * α < 1 := by
            apply lt_of_mul_lt_mul_right _ hD.le
            linarith [e2, h2d]
          have : (L : ℚ) = n := by exact_mod_cast h1
          linarith
      have h : (((d + n) * (z.1 - (e + (n - d))) + (d - n) * (z.2 - (r + (n + d))) : ℤ) : ℚ) <
          ((2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - L + 1 : ℤ) : ℚ) := by
        push_cast
        rw [hTP] at hsw_hi
        linarith [hsw_hi, hαL]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith

end FLatticePaper.Tiles.PairEvenW0P
