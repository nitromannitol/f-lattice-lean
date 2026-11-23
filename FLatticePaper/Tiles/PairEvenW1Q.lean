import FLatticePaper.Tiles.PairEvenW0Q
import FLatticePaper.Tiles.EvenIneq

/-! Task 53, item 2 (covering reduction), section 13 (continued): the even child `X = 2P + Q` at flag true (`δ = dr − ne = −1`).

The box `[α, 1] × [0, β]` is owned by the source `Q` at `2P = (2d, 2n)`. With `T = e² + 2er − r²`, `K = s_P(Q)`, `G = 2K + T`, the
`Q`-window coordinates of `z − 2P` are `t = (e+r)/2 + 2 − 2u − G v` and `s = r + G u + 4v − 2K`.
The scaled identities are `G β D = T D + 2(e − r)` and `G α D = 2K D − 2(e − r)`, with `D = 2d + e`.
The facets use the polynomial inequalities of `EvenIneq` (flag true). -/

namespace FLatticePaper.Tiles.PairEvenW1Q

open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.PairQAbox FLatticePaper.Tiles.EvenIneq
  FLatticePaper.Tiles.PairEvenW0Q

set_option maxHeartbeats 600000 in
/-- **The box `[α, 1] × [0, β]` of the flag-true even child is owned by `Q` at `2P`.** -/
theorem T1_box (d n e r : ℤ) (hd : 3 ≤ d) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v α β : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ))
    (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hu0 : α ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ β) :
    InH ⟨r, e⟩ (z.1 - 2 * d, z.2 - 2 * n) := by
  have hdetQ : (d : ℚ) * r - n * e = -1 := by exact_mod_cast hdet
  have hDi : (0 : ℤ) < 2 * d + e := by omega
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by exact_mod_cast hDi
  have hmu : muOf ⟨r, e⟩ = 1 := muQ_one r e heven
  have hf : (2 : ℚ) ≤ (e : ℚ) - r := by
    have : (2 : ℤ) ≤ e - r := by omega
    exact_mod_cast this
  have hrQ : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hdQ : (1 : ℚ) ≤ d := by exact_mod_cast (show (1 : ℤ) ≤ d by omega)
  have heQ : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℤ) < e by omega)
  have hnQ : (1 : ℚ) ≤ n := by exact_mod_cast hn
  obtain ⟨K, hK⟩ : ∃ K : ℚ, K = ((d : ℚ) + n) * e + ((d : ℚ) - n) * r := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℚ, G = 2 * K + ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) := ⟨_, rfl⟩
  have hK0 : 0 < K := by
    have h1 : (0 : ℚ) < ((d : ℚ) + n) * e := mul_pos (by linarith) heQ
    have h2 : (0 : ℚ) < ((d : ℚ) - n) * r := mul_pos (by
      have : (0 : ℚ) < (n : ℚ) := by linarith
      have hnd' : (n : ℚ) < d := by exact_mod_cast hnd
      linarith) (by linarith)
    rw [hK]; linarith
  have hT0 : (0 : ℚ) < (e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2 := by
    have h1 : (0 : ℚ) < (e : ℚ) * r := mul_pos heQ (by linarith)
    have hre' : (r : ℚ) < e := by exact_mod_cast hre
    nlinarith
  have hG0 : 0 ≤ G := by rw [hG]; linarith
  -- the two window coordinates of `z − 2P`
  have ht : (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n) =
      ((e : ℚ) + r) / 2 + 2 - 2 * u - G * v := by
    rw [hG, hK]
    linear_combination (r : ℚ) * hz1 - (e : ℚ) * hz2 + (2 * u - 2) * hdetQ
  have hs : ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n) =
      r + G * u + 4 * v - 2 * K := by
    rw [hG, hK]
    linear_combination ((e : ℚ) + r) * hz1 + ((e : ℚ) - r) * hz2 + (-4 * v) * hdetQ
  -- the scaled identities
  have hGe : G * e = ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) * (2 * d + e) + 2 * ((e : ℚ) - r) := by
    rw [hG, hK]
    linear_combination (-2 * ((e : ℚ) - r)) * hdetQ
  have hGβs : G * β * (2 * (d : ℚ) + e) = ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) * (2 * d + e) + 2 * ((e : ℚ) - r) := by
    linear_combination G * hβ + hGe
  have hGαs : G * α * (2 * (d : ℚ) + e) = 2 * K * (2 * d + e) - 2 * ((e : ℚ) - r) := by
    rw [hG, hK]
    linear_combination (2 * (((d : ℚ) + n) * e + ((d : ℚ) - n) * r) + ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2)) * hα
      + (2 * ((e : ℚ) - r)) * hdetQ
  have hα_lt : α < 1 := by
    apply lt_of_mul_lt_mul_right _ hD.le
    rw [hα]; linarith
  have hα_pos : 0 < α := by
    apply (pos_iff_pos_of_mul_pos (show 0 < α * (2 * (d : ℚ) + e) by rw [hα]; linarith)).mpr hD
  -- real bounds of the two window coordinates
  have hGv0 : 0 ≤ G * v := mul_nonneg hG0 hv0
  have hGv_le : G * v ≤ G * β := mul_le_mul_of_nonneg_left hv1 hG0
  have hGu_le : G * α ≤ G * u := mul_le_mul_of_nonneg_left hu0 hG0
  have hGu1 : G * u ≤ G := by
    have := mul_le_mul_of_nonneg_left hu1 hG0
    linarith
  have hUt : (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n) ≤ ((e : ℚ) + r) / 2 + 2 - 2 * α := by
    rw [ht]; linarith
  have hLt : ((e : ℚ) + r) / 2 - G * β ≤ (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n) := by
    rw [ht]; linarith
  have hSlo : r + G * α - 2 * K ≤ ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n) := by
    rw [hs]; linarith
  have hShi : ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n) ≤
      r + ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) + 4 * β := by
    rw [hs]; linarith [hGu1, hv1, hG]
  -- scaled facets (positivity of `x D` gives positivity of `x`)
  have hlo_key : ∀ a : ℚ, 0 < (((e : ℚ) + r) / 2 + 1 - a) * (2 * (d : ℚ) + e) - 2 * ((e : ℚ) - r) →
      a - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1 < ((e : ℚ) + r) / 2 - G * β := by
    intro a ha
    have key : (((e : ℚ) + r) / 2 - G * β - (a - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1)) * (2 * (d : ℚ) + e) =
        (((e : ℚ) + r) / 2 + 1 - a) * (2 * (d : ℚ) + e) - 2 * ((e : ℚ) - r) := by
      linear_combination (-1 : ℚ) * hGβs
    have hpos : 0 < (((e : ℚ) + r) / 2 - G * β - (a - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1)) :=
      (pos_iff_pos_of_mul_pos (by rw [key]; exact ha)).mpr hD
    linarith
  have hS_key : ∀ L : ℚ, 0 < (r + 1 - L) * (2 * (d : ℚ) + e) - 2 * ((e : ℚ) - r) →
      L - 1 < r + G * α - 2 * K := by
    intro L hL
    have key : (r + G * α - 2 * K - (L - 1)) * (2 * (d : ℚ) + e) =
        (r + 1 - L) * (2 * (d : ℚ) + e) - 2 * ((e : ℚ) - r) := by
      linear_combination hGαs
    have hpos : 0 < (r + G * α - 2 * K - (L - 1)) :=
      (pos_iff_pos_of_mul_pos (by rw [key]; exact hL)).mpr hD
    linarith
  have hhi_key : ∀ L : ℚ, 0 < (r + 1 - L) * (2 * (d : ℚ) + e) - 4 * e → 4 * β < r + 1 - L := by
    intro L hL
    have key : (r + 1 - L - 4 * β) * (2 * (d : ℚ) + e) = (r + 1 - L) * (2 * (d : ℚ) + e) - 4 * e := by
      linear_combination (-4 : ℚ) * hβ
    have hpos : 0 < (r + 1 - L - 4 * β) :=
      (pos_iff_pos_of_mul_pos (by rw [key]; exact hL)).mpr hD
    linarith
  have hBT : (4 : ℚ) * e < (r + 1) * (2 * d + e) := by
    exact_mod_cast BT_ineq d n e r hd hn hr hre hdet
  have hf2 : (0 : ℚ) < 2 * (d : ℚ) + e - (e - r) := by linarith
  have hdr : 0 < ((r : ℚ) + 1 - 0) * (2 * d + e) - 2 * ((e : ℚ) - r) := by
    have h2 : (2 : ℚ) * (2 * d + e) ≤ ((r : ℚ) + 1 - 0) * (2 * d + e) :=
      mul_le_mul_of_nonneg_right (by linarith) hD.le
    linarith
  have hBT' : 0 < ((r : ℚ) + 1 - 0) * (2 * d + e) - 4 * e := by linarith
  have hBTb : 4 * β < r + 1 - 0 := hhi_key 0 hBT'
  have hS0 : (0 : ℚ) - 1 < r + G * α - 2 * K := hS_key 0 hdr
  -- the window of `Q` at `2P`: `t` is in range by the even/odd facets below
  rcases Int.emod_two_eq_zero_or_one (z.1 - 2 * d + (z.2 - 2 * n)) with hpar | hpar
  · -- even sites: `a = min(2r, e − r)`, `l = 0`
    have hev : decide ((((z.1 - 2 * d, z.2 - 2 * n) : ℤ × ℤ).1 + (z.1 - 2 * d, z.2 - 2 * n).2) % 2 = 0) = true :=
      decide_eq_true hpar
    rw [inH_Q_iff r e (z.1 - 2 * d, z.2 - 2 * n) true hev hmu]
    have hA : aOf ⟨r, e⟩ true = min (2 * r) (e - r) := by simp [aOf]
    have hl : lOf ⟨r, e⟩ true = 0 := by simp [lOf]
    rw [hA, hl]
    dsimp only
    rcases (show 3 * r ≤ e ∨ e + 2 ≤ 3 * r by omega) with h3 | h3
    · -- `e ≥ 3r`: the minimum is `2r`
      rw [min_eq_left (show 2 * r ≤ e - r by omega)]
      have hPT : (4 : ℚ) * (e - r) < (e - 3 * r + 2) * (2 * d + e) := by
        exact_mod_cast PTlo1_ineq d n e r hd hr hre hdet heven h3
      have hk : (2 * (r : ℚ)) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1 <
          ((e : ℚ) + r) / 2 - G * β := by
        apply hlo_key
        have hid : ((((e : ℚ) + r) / 2 + 1 - 2 * r) * (2 * d + e) - 2 * ((e : ℚ) - r)) =
            (((e : ℚ) - 3 * r + 2) * (2 * d + e) - 4 * ((e : ℚ) - r)) / 2 := by ring
        rw [hid]; linarith
      have hE1 : (((2 * r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ)) : ℚ) < ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) := by
        push_cast; linarith
      have hE1' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE1)
      refine ⟨by linarith, ?_, ?_, ?_⟩
      · have h4 : ((e : ℚ) ≥ 3 * r) := by exact_mod_cast h3
        have hE2 : (((r * (z.1 - 2 * d) - e * (z.2 - 2 * n)) : ℤ) : ℚ) < ((e - r + 1 : ℤ) : ℚ) := by
          push_cast
          rcases (show e = 3 * r ∨ e ≥ 3 * r + 2 by omega) with h5 | h5
          · have hhalf : (e : ℚ) < 2 * d := by exact_mod_cast half_ineq d n e r hd hr hdet h5
            have hα2 : (1 : ℚ) < 2 * α := by
              apply lt_of_mul_lt_mul_right _ hD.le
              have e2 : 2 * α * (2 * (d : ℚ) + e) = 4 * d := by linear_combination 2 * hα
              linarith [e2, hhalf]
            have h5q : (e : ℚ) = 3 * r := by exact_mod_cast h5
            linarith
          · have h5q : (e : ℚ) ≥ 3 * r + 2 := by exact_mod_cast h5
            linarith
        have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE2)
        linarith
      · have hE3 : ((-1 : ℤ) : ℚ) < (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) := by
          push_cast; linarith
        have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE3)
        linarith
      · have hE4 : (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) < ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 + 1 : ℤ) : ℚ) := by
          push_cast; linarith
        have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE4)
        linarith
    · -- `e ≤ 3r − 2`: the minimum is `e − r`
      rw [min_eq_right (show e - r ≤ 2 * r by omega)]
      have hPT : (4 : ℚ) * (e - r) < (3 * r - e + 2) * (2 * d + e) := by
        exact_mod_cast PTlo2_ineq d n e r hd hr hre hdet heven (by omega)
      have hk : ((e : ℚ) - r) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1 <
          ((e : ℚ) + r) / 2 - G * β := by
        apply hlo_key
        have hid : ((((e : ℚ) + r) / 2 + 1 - ((e : ℚ) - r)) * (2 * d + e) - 2 * ((e : ℚ) - r)) =
            ((3 * (r : ℚ) - e + 2) * (2 * d + e) - 4 * ((e : ℚ) - r)) / 2 := by ring
        rw [hid]; linarith
      have hE1 : ((((e - r) - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ)) : ℚ) < ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) := by
        push_cast; linarith
      have hE1' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE1)
      refine ⟨by linarith, ?_, ?_, ?_⟩
      · have h4 : (e : ℚ) + 2 ≤ 3 * r := by exact_mod_cast h3
        have hE2 : (((r * (z.1 - 2 * d) - e * (z.2 - 2 * n)) : ℤ) : ℚ) < ((2 * r + 1 : ℤ) : ℚ) := by
          push_cast; linarith
        have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE2)
        linarith
      · have hE3 : ((-1 : ℤ) : ℚ) < (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) := by
          push_cast; linarith
        have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE3)
        linarith
      · have hE4 : (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) < ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 + 1 : ℤ) : ℚ) := by
          push_cast; linarith
        have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE4)
        linarith
  · -- odd sites: `a = r`, `l = min(e − r, 3r − e)`
    have hpar' : ¬ ((z.1 - 2 * d + (z.2 - 2 * n)) % 2 = 0) := by omega
    have hev : decide ((((z.1 - 2 * d, z.2 - 2 * n) : ℤ × ℤ).1 + (z.1 - 2 * d, z.2 - 2 * n).2) % 2 = 0) = false :=
      decide_eq_false hpar'
    rw [inH_Q_iff r e (z.1 - 2 * d, z.2 - 2 * n) false hev hmu]
    have hA : aOf ⟨r, e⟩ false = r := by simp [aOf]
    have hl : lOf ⟨r, e⟩ false = min (e - r) (3 * r - e) := by simp [lOf]
    rw [hA, hl]
    dsimp only
    have hO1 : (2 : ℚ) * (2 * d + e) ≤ (((e : ℚ) + r) / 2 + 1 - r) * (2 * d + e) :=
      mul_le_mul_of_nonneg_right (by linarith) hD.le
    have hk : (r : ℚ) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1 < ((e : ℚ) + r) / 2 - G * β := by
      apply hlo_key; linarith
    have hE1 : (((r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ)) : ℚ) < ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) := by
      push_cast; linarith
    have hE1' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE1)
    refine ⟨by linarith, ?_, ?_, ?_⟩
    · have hE2 : ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) < ((e + 1 : ℤ) : ℚ) := by
        push_cast; linarith
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE2)
      linarith
    · rcases (show e ≤ 2 * r ∨ 2 * r ≤ e by omega) with h2 | h2
      · rw [min_eq_left (show e - r ≤ 3 * r - e by omega)]
        have hPS : (2 : ℚ) * (e - r) < (2 * r + 1 - e) * (2 * d + e) := by
          exact_mod_cast PTslo1_ineq d e r hd hr hre h2
        have hS : ((e : ℚ) - r) - 1 < r + G * α - 2 * K := by
          apply hS_key
          have hid : ((r : ℚ) + 1 - ((e : ℚ) - r)) * (2 * d + e) = (2 * r + 1 - e) * (2 * d + e) := by ring
          rw [hid]; linarith
        have hE3 : (((e - r - 1 : ℤ)) : ℚ) < (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) := by
          push_cast; linarith
        have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE3)
        linarith
      · rw [min_eq_right (show 3 * r - e ≤ e - r by omega)]
        have hPS : (2 : ℚ) * (e - r) < (e + 1 - 2 * r) * (2 * d + e) := by
          exact_mod_cast PTslo2_ineq d e r hd hr hre h2
        have hS : (3 * (r : ℚ) - e) - 1 < r + G * α - 2 * K := by
          apply hS_key
          have hid : ((r : ℚ) + 1 - (3 * (r : ℚ) - e)) * (2 * d + e) = (e + 1 - 2 * r) * (2 * d + e) := by ring
          rw [hid]; linarith
        have hE3 : (((3 * r - e - 1 : ℤ)) : ℚ) < (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) := by
          push_cast; linarith
        have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE3)
        linarith
    · rcases (show e ≤ 2 * r ∨ 2 * r ≤ e by omega) with h2 | h2
      · rw [min_eq_left (show e - r ≤ 3 * r - e by omega)]
        have hPA : (4 : ℚ) * e < (2 * r + 1 - e) * (2 * d + e) := by
          exact_mod_cast A1T_ineq d n e r hd hr hre hdet heven h2
        have hB : 4 * β < r + 1 - ((e : ℚ) - r) := by
          apply hhi_key
          have hid : ((r : ℚ) + 1 - ((e : ℚ) - r)) * (2 * d + e) = (2 * r + 1 - e) * (2 * d + e) := by ring
          rw [hid]; linarith
        have hE4 : (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) < ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (e - r) + 1 : ℤ) : ℚ) := by
          push_cast; linarith
        have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE4)
        linarith
      · rw [min_eq_right (show 3 * r - e ≤ e - r by omega)]
        have hPA : (4 : ℚ) * e < (e + 1 - 2 * r) * (2 * d + e) := by
          exact_mod_cast A2T_ineq d n e r hd hr hre hdet heven h2
        have hB : 4 * β < r + 1 - ((3 : ℚ) * r - e) := by
          apply hhi_key
          have hid : ((r : ℚ) + 1 - (3 * r - e)) * (2 * d + e) = (e + 1 - 2 * r) * (2 * d + e) := by ring
          rw [hid]; linarith
        have hE4 : (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) < ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (3 * r - e) + 1 : ℤ) : ℚ) := by
          push_cast; linarith
        have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE4)
        linarith

end FLatticePaper.Tiles.PairEvenW1Q
