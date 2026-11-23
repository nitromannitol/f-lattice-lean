import FLatticePaper.Tiles.PairEvenW0Q
import FLatticePaper.Tiles.EvenIneq
import FLatticePaper.Tiles.EvenP21

/-! Task 53, item 2 (covering reduction), section 13 (continued): the even child `X = 2P + Q` at flag true (`δ = dr − ne = −1`).

The box `[α, 1] × [0, β]` is owned by the source `Q` at `2P = (2d, 2n)`. With `T = e² + 2er − r²`, `K = s_P(Q)`, `G = 2K + T`, the
`Q`-window coordinates of `z − 2P` are `t = (e+r)/2 + 2 − 2u − G v` and `s = r + G u + 4v − 2K`.
The scaled identities are `G β D = T D + 2(e − r)` and `G α D = 2K D − 2(e − r)`, with `D = 2d + e`.

The proof is split into four case lemmas (the even and odd sites, and the branches of the minimum), so that each declaration stays
under the default heartbeat limit. `T1_box` gives the common real facts and dispatches on the parity and the branch. -/

namespace FLatticePaper.Tiles.PairEvenW1Q

open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.PairQAbox FLatticePaper.Tiles.EvenIneq
  FLatticePaper.Tiles.PairEvenW0Q

/-- Even sites, `3r ≤ e`: the minimum `min(2r, e − r)` is `2r`. -/
theorem T1_even_ge (d n e r : ℤ) (z : ℤ × ℤ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0) (h3 : 3 * r ≤ e)
    (hpar : (z.1 - 2 * d + (z.2 - 2 * n)) % 2 = 0)
    (α β G K : ℚ) (hD : (0 : ℚ) < 2 * (d : ℚ) + e)
    (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ))
    (hGβs : G * β * (2 * (d : ℚ) + e) = ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) * (2 * d + e) + 2 * ((e : ℚ) - r))
    (hGαs : G * α * (2 * (d : ℚ) + e) = 2 * K * (2 * d + e) - 2 * ((e : ℚ) - r))
    (hUt : (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n) ≤ ((e : ℚ) + r) / 2 + 2 - 2 * α)
    (hLt : ((e : ℚ) + r) / 2 - G * β ≤ (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n))
    (hSlo : (r : ℚ) + G * α - 2 * K ≤ ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n))
    (hShi : ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n) ≤
      r + ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) + 4 * β)
    (hα_pos : 0 < α) (hBTb : 4 * β < (r : ℚ) + 1) :
    InH ⟨r, e⟩ (z.1 - 2 * d, z.2 - 2 * n) := by
  have hmu : muOf ⟨r, e⟩ = 1 := muQ_one r e heven
  have hrq : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hdQ : (2 : ℚ) ≤ d := by exact_mod_cast hd
  have hev : decide ((z.1 - 2 * d + (z.2 - 2 * n)) % 2 = 0) = true := decide_eq_true hpar
  rw [inH_Q_iff r e (z.1 - 2 * d, z.2 - 2 * n) true hev hmu]
  have hA : aOf ⟨r, e⟩ true = min (2 * r) (e - r) := by simp [aOf]
  have hl : lOf ⟨r, e⟩ true = 0 := by simp [lOf]
  rw [hA, hl, min_eq_left (show 2 * r ≤ e - r by omega)]
  dsimp only
  have hPT : (4 : ℚ) * (e - r) < (e - 3 * r + 2) * (2 * d + e) := by
    exact_mod_cast PTlo1_ineq d n e r hd hr hre hdet heven h3
  have hk : (2 : ℚ) * r - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1 < ((e : ℚ) + r) / 2 - G * β := by
    have key : (((e : ℚ) + r) / 2 - G * β - (2 * r - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1)) * (2 * (d : ℚ) + e) =
        (((e : ℚ) + r) / 2 + 1 - 2 * r) * (2 * (d : ℚ) + e) - 2 * ((e : ℚ) - r) := by
      linear_combination (-1 : ℚ) * hGβs
    have hid : (((e : ℚ) + r) / 2 + 1 - 2 * r) * (2 * (d : ℚ) + e) - 2 * ((e : ℚ) - r) =
        (((e : ℚ) - 3 * r + 2) * (2 * (d : ℚ) + e) - 4 * ((e : ℚ) - r)) / 2 := by ring
    have hpos : 0 < (((e : ℚ) + r) / 2 - G * β - (2 * r - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1)) :=
      (pos_iff_pos_of_mul_pos (by rw [key, hid]; linarith only [hPT])).mpr hD
    linarith only [hpos]
  have hE1 : ((2 * r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) < ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) := by
    push_cast; linarith only [hk, hLt]
  have hE1' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE1)
  refine ⟨by linarith only [hE1'], ?_, ?_, ?_⟩
  · have hE2 : ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) < ((e - r + 1 : ℤ) : ℚ) := by
      push_cast
      rcases (show e = 3 * r ∨ 3 * r + 2 ≤ e by omega) with h5 | h5
      · have hhalf : (e : ℚ) < 2 * d := by exact_mod_cast half_ineq d n e r hd hr hdet h5
        have hα2 : (1 : ℚ) < 2 * α := by
          apply lt_of_mul_lt_mul_right _ hD.le
          have e2 : 2 * α * (2 * (d : ℚ) + e) = 4 * d := by linear_combination 2 * hα
          linarith only [e2, hhalf]
        have h5q : (e : ℚ) = 3 * r := by exact_mod_cast h5
        linarith only [hUt, hα2, h5q]
      · have h5q : (e : ℚ) ≥ 3 * r + 2 := by exact_mod_cast h5
        linarith only [hUt, hα_pos, h5q]
    have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE2)
    linarith only [h']
  · have hdr : 0 < ((r : ℚ) + 1 - 0) * (2 * d + e) - 2 * ((e : ℚ) - r) := by
      have h2 : (2 : ℚ) * (2 * d + e) ≤ ((r : ℚ) + 1 - 0) * (2 * d + e) :=
        mul_le_mul_of_nonneg_right (by linarith only [hrq]) hD.le
      have hdd : (0 : ℚ) < 2 * d := by linarith only [hdQ]
      linarith only [h2, hdd, hrq]
    have hS0 : (0 : ℚ) - 1 < r + G * α - 2 * K := by
      have key : (r + G * α - 2 * K - (0 - 1)) * (2 * (d : ℚ) + e) = ((r : ℚ) + 1 - 0) * (2 * d + e) - 2 * ((e : ℚ) - r) := by
        linear_combination hGαs
      have hpos : 0 < (r + G * α - 2 * K - (0 - 1)) :=
        (pos_iff_pos_of_mul_pos (by rw [key]; exact hdr)).mpr hD
      linarith only [hpos]
    have hE3 : ((-1 : ℤ) : ℚ) < (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) := by
      push_cast; linarith only [hSlo, hS0]
    have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE3)
    linarith only [h']
  · have hE4 : (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) <
        ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 + 1 : ℤ) : ℚ) := by
      push_cast; linarith only [hShi, hBTb]
    have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE4)
    linarith only [h']

/-- Even sites, `e + 2 ≤ 3r`: the minimum `min(2r, e − r)` is `e − r`. -/
theorem T1_even_lt (d n e r : ℤ) (z : ℤ × ℤ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0) (h3 : e + 2 ≤ 3 * r)
    (hpar : (z.1 - 2 * d + (z.2 - 2 * n)) % 2 = 0)
    (α β G K : ℚ) (hD : (0 : ℚ) < 2 * (d : ℚ) + e)
    (hGβs : G * β * (2 * (d : ℚ) + e) = ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) * (2 * d + e) + 2 * ((e : ℚ) - r))
    (hGαs : G * α * (2 * (d : ℚ) + e) = 2 * K * (2 * d + e) - 2 * ((e : ℚ) - r))
    (hUt : (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n) ≤ ((e : ℚ) + r) / 2 + 2 - 2 * α)
    (hLt : ((e : ℚ) + r) / 2 - G * β ≤ (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n))
    (hSlo : (r : ℚ) + G * α - 2 * K ≤ ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n))
    (hShi : ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n) ≤
      r + ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) + 4 * β)
    (hα_pos : 0 < α) (hBTb : 4 * β < (r : ℚ) + 1) :
    InH ⟨r, e⟩ (z.1 - 2 * d, z.2 - 2 * n) := by
  have hmu : muOf ⟨r, e⟩ = 1 := muQ_one r e heven
  have hrq : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hdQ : (2 : ℚ) ≤ d := by exact_mod_cast hd
  have hev : decide ((z.1 - 2 * d + (z.2 - 2 * n)) % 2 = 0) = true := decide_eq_true hpar
  rw [inH_Q_iff r e (z.1 - 2 * d, z.2 - 2 * n) true hev hmu]
  have hA : aOf ⟨r, e⟩ true = min (2 * r) (e - r) := by simp [aOf]
  have hl : lOf ⟨r, e⟩ true = 0 := by simp [lOf]
  rw [hA, hl, min_eq_right (show e - r ≤ 2 * r by omega)]
  dsimp only
  have hPT : (4 : ℚ) * (e - r) < (3 * r - e + 2) * (2 * d + e) := by
    exact_mod_cast PTlo2_ineq d n e r hd hr hre hdet heven (by omega)
  have hk : ((e : ℚ) - r) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1 < ((e : ℚ) + r) / 2 - G * β := by
    have key : (((e : ℚ) + r) / 2 - G * β - (((e : ℚ) - r) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1)) *
        (2 * (d : ℚ) + e) = (((e : ℚ) + r) / 2 + 1 - ((e : ℚ) - r)) * (2 * (d : ℚ) + e) - 2 * ((e : ℚ) - r) := by
      linear_combination (-1 : ℚ) * hGβs
    have hid : (((e : ℚ) + r) / 2 + 1 - ((e : ℚ) - r)) * (2 * (d : ℚ) + e) - 2 * ((e : ℚ) - r) =
        ((3 * (r : ℚ) - e + 2) * (2 * (d : ℚ) + e) - 4 * ((e : ℚ) - r)) / 2 := by ring
    have hpos : 0 < (((e : ℚ) + r) / 2 - G * β - (((e : ℚ) - r) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1)) :=
      (pos_iff_pos_of_mul_pos (by rw [key, hid]; linarith only [hPT])).mpr hD
    linarith only [hpos]
  have hE1 : (((e - r) - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) < ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) := by
    push_cast; linarith only [hk, hLt]
  have hE1' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE1)
  refine ⟨by linarith only [hE1'], ?_, ?_, ?_⟩
  · have h4 : (e : ℚ) + 2 ≤ 3 * r := by exact_mod_cast h3
    have hE2 : ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) < ((2 * r + 1 : ℤ) : ℚ) := by
      push_cast; linarith only [hUt, hα_pos, h4]
    have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE2)
    linarith only [h']
  · have hdr : 0 < ((r : ℚ) + 1 - 0) * (2 * d + e) - 2 * ((e : ℚ) - r) := by
      have h2 : (2 : ℚ) * (2 * d + e) ≤ ((r : ℚ) + 1 - 0) * (2 * d + e) :=
        mul_le_mul_of_nonneg_right (by linarith only [hrq]) hD.le
      have hdd : (0 : ℚ) < 2 * d := by linarith only [hdQ]
      linarith only [h2, hdd, hrq]
    have hS0 : (0 : ℚ) - 1 < r + G * α - 2 * K := by
      have key : (r + G * α - 2 * K - (0 - 1)) * (2 * (d : ℚ) + e) = ((r : ℚ) + 1 - 0) * (2 * d + e) - 2 * ((e : ℚ) - r) := by
        linear_combination hGαs
      have hpos : 0 < (r + G * α - 2 * K - (0 - 1)) :=
        (pos_iff_pos_of_mul_pos (by rw [key]; exact hdr)).mpr hD
      linarith only [hpos]
    have hE3 : ((-1 : ℤ) : ℚ) < (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) := by
      push_cast; linarith only [hSlo, hS0]
    have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE3)
    linarith only [h']
  · have hE4 : (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) <
        ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 + 1 : ℤ) : ℚ) := by
      push_cast; linarith only [hShi, hBTb]
    have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE4)
    linarith only [h']

/-- Odd sites, `e ≤ 2r`: the minimum `min(e − r, 3r − e)` is `e − r`. -/
theorem T1_odd_le (d n e r : ℤ) (z : ℤ × ℤ) (hd : 3 ≤ d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0) (h2 : e ≤ 2 * r)
    (hpar : (z.1 - 2 * d + (z.2 - 2 * n)) % 2 = 1)
    (α β G K : ℚ) (hD : (0 : ℚ) < 2 * (d : ℚ) + e) (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hGβs : G * β * (2 * (d : ℚ) + e) = ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) * (2 * d + e) + 2 * ((e : ℚ) - r))
    (hGαs : G * α * (2 * (d : ℚ) + e) = 2 * K * (2 * d + e) - 2 * ((e : ℚ) - r))
    (hUt : (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n) ≤ ((e : ℚ) + r) / 2 + 2 - 2 * α)
    (hLt : ((e : ℚ) + r) / 2 - G * β ≤ (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n))
    (hSlo : (r : ℚ) + G * α - 2 * K ≤ ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n))
    (hShi : ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n) ≤
      r + ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) + 4 * β)
    (hα_pos : 0 < α) :
    InH ⟨r, e⟩ (z.1 - 2 * d, z.2 - 2 * n) := by
  have hmu : muOf ⟨r, e⟩ = 1 := muQ_one r e heven
  have hrq : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hev : decide ((z.1 - 2 * d + (z.2 - 2 * n)) % 2 = 0) = false := decide_eq_false (by omega)
  rw [inH_Q_iff r e (z.1 - 2 * d, z.2 - 2 * n) false hev hmu]
  have hA : aOf ⟨r, e⟩ false = r := by simp [aOf]
  have hl : lOf ⟨r, e⟩ false = min (e - r) (3 * r - e) := by simp [lOf]
  rw [hA, hl, min_eq_left (show e - r ≤ 3 * r - e by omega)]
  dsimp only
  have hf2 : (2 : ℚ) ≤ (e : ℚ) - r := by exact_mod_cast (show (2 : ℤ) ≤ e - r by omega)
  have hdq : (3 : ℚ) ≤ d := by exact_mod_cast hd
  have hO1 : (2 : ℚ) * (2 * d + e) ≤ (((e : ℚ) + r) / 2 + 1 - r) * (2 * d + e) :=
    mul_le_mul_of_nonneg_right (by linarith only [hf2]) hD.le
  have hk : (r : ℚ) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1 < ((e : ℚ) + r) / 2 - G * β := by
    have key : (((e : ℚ) + r) / 2 - G * β - ((r : ℚ) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1)) *
        (2 * (d : ℚ) + e) = (((e : ℚ) + r) / 2 + 1 - r) * (2 * (d : ℚ) + e) - 2 * ((e : ℚ) - r) := by
      linear_combination (-1 : ℚ) * hGβs
    have hpos : 0 < (((e : ℚ) + r) / 2 - G * β - ((r : ℚ) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1)) :=
      (pos_iff_pos_of_mul_pos (by rw [key]; linarith only [hO1, hdq, hrq])).mpr hD
    linarith only [hpos]
  have hE1 : ((r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) < ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) := by
    push_cast; linarith only [hk, hLt]
  have hE1' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE1)
  refine ⟨by linarith only [hE1'], ?_, ?_, ?_⟩
  · have hE2 : ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) < ((e + 1 : ℤ) : ℚ) := by
      push_cast; linarith only [hUt, hα_pos, hf2]
    have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE2)
    linarith only [h']
  · have hS : ((e : ℚ) - r) - 1 < r + G * α - 2 * K := by
      apply (show ∀ L : ℚ, 0 < (r + 1 - L) * (2 * (d : ℚ) + e) - 2 * ((e : ℚ) - r) →
          L - 1 < r + G * α - 2 * K from ?_) _ (by
        have hid : ((r : ℚ) + 1 - ((e : ℚ) - r)) * (2 * (d : ℚ) + e) = (2 * r + 1 - e) * (2 * d + e) := by ring
        have hPS : (2 : ℚ) * (e - r) < (2 * r + 1 - e) * (2 * d + e) := by
          exact_mod_cast PTslo1_ineq d e r (by omega) hr hre h2
        linarith only [hid, hPS])
      intro L hL
      have key : (r + G * α - 2 * K - (L - 1)) * (2 * (d : ℚ) + e) = (r + 1 - L) * (2 * (d : ℚ) + e) - 2 * ((e : ℚ) - r) := by
        linear_combination hGαs
      have hpos : 0 < (r + G * α - 2 * K - (L - 1)) := (pos_iff_pos_of_mul_pos (by rw [key]; exact hL)).mpr hD
      linarith only [hpos]
    have hE3 : (((e - r - 1 : ℤ)) : ℚ) < (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) := by
      push_cast; linarith only [hSlo, hS]
    have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE3)
    linarith only [h']
  · have hB : 4 * β < (r : ℚ) + 1 - ((e : ℚ) - r) := by
      have hPA : (4 : ℚ) * e < (2 * r + 1 - e) * (2 * d + e) := by
        exact_mod_cast A1T_ineq d n e r hd hr hre hdet heven h2
      have key : ((r : ℚ) + 1 - ((e : ℚ) - r) - 4 * β) * (2 * (d : ℚ) + e) =
          ((r : ℚ) + 1 - ((e : ℚ) - r)) * (2 * (d : ℚ) + e) - 4 * e := by
        linear_combination (-4 : ℚ) * hβ
      have hid : ((r : ℚ) + 1 - ((e : ℚ) - r)) * (2 * (d : ℚ) + e) = (2 * r + 1 - e) * (2 * d + e) := by ring
      have hpos : 0 < ((r : ℚ) + 1 - ((e : ℚ) - r) - 4 * β) :=
        (pos_iff_pos_of_mul_pos (by rw [key, hid]; linarith only [hPA])).mpr hD
      linarith only [hpos]
    have hE4 : (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) <
        ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (e - r) + 1 : ℤ) : ℚ) := by
      push_cast; linarith only [hShi, hB]
    have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE4)
    linarith only [h']

/-- The finite check at `(d,n,e,r) = (2,1,3,1)`: the odd-site upper facet `2 z₁ + z₂ ≤ 18` on the box. -/
theorem T1_fin31 (z1 z2 : ℤ) (u v : ℚ)
    (hz1 : (z1 : ℚ) - 1 / 2 = u * 7 - v * 4) (hz2 : (z2 : ℚ) + 1 / 2 = u * 3 + v * 10)
    (hu0 : 4 / 7 ≤ u) (hu1 : u ≤ 1) (hv1 : v ≤ 3 / 7) : 2 * z1 + z2 ≤ 18 := by
  have hA : (82 : ℚ) * u = 10 * z1 + 4 * z2 - 3 := by linear_combination (-10 : ℚ) * hz1 - 4 * hz2
  have hB : (82 : ℚ) * v = 7 * z2 - 3 * z1 + 5 := by linear_combination 3 * hz1 - 7 * hz2
  have h1 : (328 : ℚ) ≤ 7 * (10 * z1 + 4 * z2 - 3) := by linarith
  have h2 : (7 : ℚ) * (7 * z2 - 3 * z1 + 5) ≤ 246 := by linarith
  have h3 : (10 : ℚ) * z1 + 4 * z2 - 3 ≤ 82 := by linarith
  have h1' : (328 : ℤ) ≤ 7 * (10 * z1 + 4 * z2 - 3) := by exact_mod_cast h1
  have h2' : (7 : ℤ) * (7 * z2 - 3 * z1 + 5) ≤ 246 := by exact_mod_cast h2
  have h3' : (10 : ℤ) * z1 + 4 * z2 - 3 ≤ 82 := by exact_mod_cast h3
  omega

/-- Odd sites, `2r ≤ e`: the minimum `min(e − r, 3r − e)` is `3r − e`. For `d = 2` the upper facet is the lattice step
`T1_lat` (`r ≥ 3`) or the finite check `T1_fin31` (`r = 1`). -/
theorem T1_odd_ge (d n e r : ℤ) (z : ℤ × ℤ) (hd : 2 ≤ d) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0) (h2 : 2 * r ≤ e)
    (hpar : (z.1 - 2 * d + (z.2 - 2 * n)) % 2 = 1)
    (α β G K u v : ℚ) (hD : (0 : ℚ) < 2 * (d : ℚ) + e) (hα : α * (2 * (d : ℚ) + e) = 2 * (d : ℚ))
    (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hu0 : α ≤ u) (hu1 : u ≤ 1) (hv1 : v ≤ β)
    (hGβs : G * β * (2 * (d : ℚ) + e) = ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) * (2 * d + e) + 2 * ((e : ℚ) - r))
    (hGαs : G * α * (2 * (d : ℚ) + e) = 2 * K * (2 * d + e) - 2 * ((e : ℚ) - r))
    (hUt : (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n) ≤ ((e : ℚ) + r) / 2 + 2 - 2 * α)
    (hLt : ((e : ℚ) + r) / 2 - G * β ≤ (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n))
    (hSlo : (r : ℚ) + G * α - 2 * K ≤ ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n))
    (hShi : ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n) ≤
      r + ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) + 4 * β)
    (hα_pos : 0 < α) :
    InH ⟨r, e⟩ (z.1 - 2 * d, z.2 - 2 * n) := by
  have hmu : muOf ⟨r, e⟩ = 1 := muQ_one r e heven
  have hrq : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hev : decide ((z.1 - 2 * d + (z.2 - 2 * n)) % 2 = 0) = false := decide_eq_false (by omega)
  rw [inH_Q_iff r e (z.1 - 2 * d, z.2 - 2 * n) false hev hmu]
  have hA : aOf ⟨r, e⟩ false = r := by simp [aOf]
  have hl : lOf ⟨r, e⟩ false = min (e - r) (3 * r - e) := by simp [lOf]
  rw [hA, hl, min_eq_right (show 3 * r - e ≤ e - r by omega)]
  dsimp only
  have hf2 : (2 : ℚ) ≤ (e : ℚ) - r := by exact_mod_cast (show (2 : ℤ) ≤ e - r by omega)
  have hdq : (2 : ℚ) ≤ d := by exact_mod_cast hd
  have hO1 : (2 : ℚ) * (2 * d + e) ≤ (((e : ℚ) + r) / 2 + 1 - r) * (2 * d + e) :=
    mul_le_mul_of_nonneg_right (by linarith only [hf2]) hD.le
  have hk : (r : ℚ) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1 < ((e : ℚ) + r) / 2 - G * β := by
    have key : (((e : ℚ) + r) / 2 - G * β - ((r : ℚ) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1)) *
        (2 * (d : ℚ) + e) = (((e : ℚ) + r) / 2 + 1 - r) * (2 * (d : ℚ) + e) - 2 * ((e : ℚ) - r) := by
      linear_combination (-1 : ℚ) * hGβs
    have hpos : 0 < (((e : ℚ) + r) / 2 - G * β - ((r : ℚ) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) - 1)) :=
      (pos_iff_pos_of_mul_pos (by rw [key]; linarith only [hO1, hdq, hrq])).mpr hD
    linarith only [hpos]
  have hE1 : (((r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ)) : ℚ) < ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) := by
    push_cast; linarith only [hk, hLt]
  have hE1' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE1)
  refine ⟨by linarith only [hE1'], ?_, ?_, ?_⟩
  · have hE2 : ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) < ((e + 1 : ℤ) : ℚ) := by
      push_cast; linarith only [hUt, hα_pos, hf2]
    have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE2)
    linarith only [h']
  · have hS : (3 * (r : ℚ) - e) - 1 < r + G * α - 2 * K := by
      have hid : ((r : ℚ) + 1 - (3 * (r : ℚ) - e)) * (2 * (d : ℚ) + e) = (e + 1 - 2 * r) * (2 * d + e) := by ring
      have hPS : (2 : ℚ) * (e - r) < (e + 1 - 2 * r) * (2 * d + e) := by
        have hPSz := PTslo2_ineq d e r hd hr hre h2
        exact_mod_cast hPSz
      have key : (r + G * α - 2 * K - ((3 * (r : ℚ) - e) - 1)) * (2 * (d : ℚ) + e) =
          ((r : ℚ) + 1 - (3 * (r : ℚ) - e)) * (2 * (d : ℚ) + e) - 2 * ((e : ℚ) - r) := by
        linear_combination hGαs
      have hpos : 0 < (r + G * α - 2 * K - ((3 * (r : ℚ) - e) - 1)) :=
        (pos_iff_pos_of_mul_pos (by rw [key, hid]; linarith only [hPS])).mpr hD
      linarith only [hpos]
    have hE3 : (((3 * r - e - 1 : ℤ)) : ℚ) < (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) := by
      push_cast; linarith only [hSlo, hS]
    have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp hE3)
    linarith only [h']
  · -- the upper `s` facet
    rcases (show d = 2 ∨ 3 ≤ d by omega) with hd2 | hd3
    · -- `d = 2`: `n = 1`, `e = 2r + 1`
      have hn1 : n = 1 := by omega
      have he : e = 2 * r + 1 := by subst hd2; subst hn1; omega
      subst hd2
      subst hn1
      subst he
      have hz1' : (z.1 : ℚ) - 1 / 2 = u * (2 * (r : ℚ) + 5) - v * ((r : ℚ) + 3) := by
        push_cast at hz1; linear_combination hz1
      have hz2' : (z.2 : ℚ) + 1 / 2 = u * ((r : ℚ) + 2) + v * (3 * (r : ℚ) + 7) := by
        push_cast at hz2; linear_combination hz2
      have hβ' : β * (2 * (r : ℚ) + 5) = 2 * (r : ℚ) + 1 := by
        push_cast at hβ; linear_combination hβ
      rcases (show r = 1 ∨ 3 ≤ r by omega) with hr1 | hr3
      · subst hr1
        have hz1'' : (z.1 : ℚ) - 1 / 2 = u * 7 - v * 4 := by linear_combination hz1'
        have hz2'' : (z.2 : ℚ) + 1 / 2 = u * 3 + v * 10 := by linear_combination hz2'
        have hα7 : α * 7 = 4 := by push_cast at hα; linear_combination hα
        have hu0' : (4 : ℚ) / 7 ≤ u := by linarith
        have hv1' : v ≤ 3 / 7 := by
          have hβ7 : β * 7 = 3 := by push_cast at hβ; linear_combination hβ
          linarith
        have hfin := T1_fin31 z.1 z.2 u v hz1'' hz2'' hu0' hu1 hv1'
        push_cast
        omega
      · obtain ⟨m, hm⟩ : ∃ m : ℤ, r = 2 * m + 1 := ⟨(r - 1) / 2, by omega⟩
        have hm1 : 1 ≤ m := by omega
        have hL := FLatticePaper.Tiles.EvenP21.T1_lat r m z.1 z.2 hm hm1 u v β hz1' hz2' hβ' hu1 hv1
        push_cast
        linarith [hL]
    · -- `d ≥ 3`: the real facet `A2T`
      have hPA : (4 : ℚ) * e < (e + 1 - 2 * r) * (2 * d + e) := by
        exact_mod_cast A2T_ineq d n e r hd3 hr hre hdet heven h2
      have hB : 4 * β < (r : ℚ) + 1 - (3 * (r : ℚ) - e) := by
        have key : ((r : ℚ) + 1 - (3 * (r : ℚ) - e) - 4 * β) * (2 * (d : ℚ) + e) =
            ((r : ℚ) + 1 - (3 * (r : ℚ) - e)) * (2 * (d : ℚ) + e) - 4 * e := by
          linear_combination (-4 : ℚ) * hβ
        have hid : ((r : ℚ) + 1 - (3 * (r : ℚ) - e)) * (2 * (d : ℚ) + e) = (e + 1 - 2 * r) * (2 * d + e) := by ring
        have hpos : 0 < ((r : ℚ) + 1 - (3 * (r : ℚ) - e) - 4 * β) :=
          (pos_iff_pos_of_mul_pos (by rw [key, hid]; linarith only [hPA])).mpr hD
        linarith only [hpos]
      have hE4 : (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) <
          ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (3 * r - e) + 1 : ℤ) : ℚ) := by
        push_cast; linarith only [hShi, hB]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp hE4)
      linarith only [h']

/-- **The box `[α, 1] × [0, β]` of the flag-true even child is owned by `Q` at `2P`.** -/
theorem T1_box (d n e r : ℤ) (hd : 2 ≤ d) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
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
  have hrQ : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hdQ : (2 : ℚ) ≤ d := by exact_mod_cast hd
  have heQ : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℤ) < e by omega)
  have hnQ : (1 : ℚ) ≤ n := by exact_mod_cast hn
  obtain ⟨K, hK⟩ : ∃ K : ℚ, K = ((d : ℚ) + n) * e + ((d : ℚ) - n) * r := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℚ, G = 2 * K + ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) := ⟨_, rfl⟩
  have hK0 : 0 < K := by
    have hndQ : (n : ℚ) < d := by exact_mod_cast hnd
    have h1 : (0 : ℚ) < ((d : ℚ) + n) * e := mul_pos (by linarith only [hdQ, hnQ]) heQ
    have h2 : (0 : ℚ) < ((d : ℚ) - n) * r := mul_pos (by linarith only [hndQ]) (by linarith only [hrQ])
    rw [hK]; linarith only [h1, h2]
  have hT0 : (0 : ℚ) < (e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2 := by
    have h1 : (0 : ℚ) < (e : ℚ) * r := mul_pos heQ (by linarith only [hrQ])
    have hre' : (r : ℚ) < e := by exact_mod_cast hre
    have h2 : (e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2 = ((e : ℚ) - r) * ((e : ℚ) + r) + 2 * ((e : ℚ) * r) := by ring
    have h3 : (0 : ℚ) < ((e : ℚ) - r) * ((e : ℚ) + r) := mul_pos (by linarith only [hre']) (by linarith only [hre', hrQ])
    rw [h2]; linarith only [h1, h3]
  have hG0 : 0 ≤ G := by rw [hG]; linarith only [hK0, hT0]
  have ht : (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n) =
      ((e : ℚ) + r) / 2 + 2 - 2 * u - G * v := by
    rw [hG, hK]
    linear_combination (r : ℚ) * hz1 - (e : ℚ) * hz2 + (2 * u - 2) * hdetQ
  have hs : ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n) =
      r + G * u + 4 * v - 2 * K := by
    rw [hG, hK]
    linear_combination ((e : ℚ) + r) * hz1 + ((e : ℚ) - r) * hz2 + (-4 * v) * hdetQ
  have hGe : G * e = ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) * (2 * d + e) + 2 * ((e : ℚ) - r) := by
    rw [hG, hK]
    linear_combination (-2 * ((e : ℚ) - r)) * hdetQ
  have hGβs : G * β * (2 * (d : ℚ) + e) = ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) * (2 * d + e) + 2 * ((e : ℚ) - r) := by
    linear_combination G * hβ + hGe
  have hGαs : G * α * (2 * (d : ℚ) + e) = 2 * K * (2 * d + e) - 2 * ((e : ℚ) - r) := by
    rw [hG, hK]
    linear_combination (2 * (((d : ℚ) + n) * e + ((d : ℚ) - n) * r) + ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2)) * hα
      + (2 * ((e : ℚ) - r)) * hdetQ
  have hα_pos : 0 < α := by
    apply (pos_iff_pos_of_mul_pos (show 0 < α * (2 * (d : ℚ) + e) by rw [hα]; linarith only [hdQ])).mpr hD
  have hGv0 : 0 ≤ G * v := mul_nonneg hG0 (by linarith only [hv0])
  have hGv_le : G * v ≤ G * β := mul_le_mul_of_nonneg_left hv1 hG0
  have hGu_le : G * α ≤ G * u := mul_le_mul_of_nonneg_left hu0 hG0
  have hGu1 : G * u ≤ G := by
    have := mul_le_mul_of_nonneg_left hu1 hG0
    linarith only [this]
  have hUt : (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n) ≤ ((e : ℚ) + r) / 2 + 2 - 2 * α := by
    rw [ht]; linarith only [hGv0, hu0]
  have hLt : ((e : ℚ) + r) / 2 - G * β ≤ (r : ℚ) * (z.1 - 2 * d) - e * (z.2 - 2 * n) := by
    rw [ht]; linarith only [hGv_le, hu1]
  have hSlo : (r : ℚ) + G * α - 2 * K ≤ ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n) := by
    rw [hs]; linarith only [hGu_le, hv0]
  have hShi : ((e : ℚ) + r) * (z.1 - 2 * d) + ((e : ℚ) - r) * (z.2 - 2 * n) ≤
      r + ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) + 4 * β := by
    rw [hs]; linarith only [hGu1, hv1, hG]
  have hBTq : (4 : ℚ) * e < (r + 1) * (2 * d + e) := by
    exact_mod_cast BT_ineq d n e r hd hn hr hre hdet
  have hBTb : 4 * β < (r : ℚ) + 1 := four_beta_lt hD hβ hBTq
  rcases Int.emod_two_eq_zero_or_one (z.1 - 2 * d + (z.2 - 2 * n)) with hpar | hpar
  · rcases (show 3 * r ≤ e ∨ e + 2 ≤ 3 * r by omega) with h3 | h3
    · exact T1_even_ge d n e r z hd hr hre hdet heven h3 hpar α β G K hD hα hGβs hGαs hUt hLt hSlo hShi hα_pos hBTb
    · exact T1_even_lt d n e r z hd hr hre hdet heven h3 hpar α β G K hD hGβs hGαs hUt hLt hSlo hShi hα_pos hBTb
  · rcases (show e ≤ 2 * r ∨ 2 * r ≤ e by omega) with h2 | h2
    · -- `e ≤ 2r`: impossible for `d = 2` (then `e = 2r + 1`), otherwise the `A1T` branch
      rcases (show d = 2 ∨ 3 ≤ d by omega) with hd2 | hd3
      · subst hd2
        have hn1 : n = 1 := by omega
        subst hn1
        omega
      · exact T1_odd_le d n e r z hd3 hr hre hdet heven h2 hpar α β G K hD hβ hGβs hGαs hUt hLt hSlo hShi hα_pos
    · exact T1_odd_ge d n e r z hd hn hnd hr hre hdet heven h2 hpar α β G K u v hD hα hβ hz1 hz2 hu0 hu1 hv1
        hGβs hGαs hUt hLt hSlo hShi hα_pos

end FLatticePaper.Tiles.PairEvenW1Q
