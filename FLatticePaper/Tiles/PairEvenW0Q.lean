import FLatticePaper.Tiles.PairQAbox
import FLatticePaper.Tiles.EvenIneq

/-! Task 53, item 2 (covering reduction), section 13: the even child `X = 2P + Q` at flag false (`δ = dr − ne = +1`).

The cell of `X` has periods `U = (2d+e, 2n+r)` and `V = (2n+r−2d−e, 2d+e+2n+r)`, with `β = e/(2d+e)`. The box `[0, β]²` is
owned by the single source `Q` at `0`: every integer point `z` of the box lies in `H_Q`. Parity splits are by `z₁ + z₂`.

The real facets use `t_Q(z) = (e+r)/2 + 2u − G v`, `s_Q(z) = r + G u − 4v` with `G = 2K + T_Q`, `K = s_P(Q)`, `T_Q = e² + 2er − r²`,
and the identity `G e = T_Q D − 2(e − r)`. Integer rounding uses the strict real bounds (`B`, `A1`, `A2`, `C1`, `C2` of `EvenIneq`). -/

namespace FLatticePaper.Tiles.PairEvenW0Q

open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.PairQAbox FLatticePaper.Tiles.EvenIneq

/-- The window of `Q = (e, r)` is `μ = 1` (since `e + r` is even). -/
theorem muQ_one (r e : ℤ) (heven : (e + r) % 2 = 0) : muOf ⟨r, e⟩ = 1 := by
  show (if (r + e) % 2 = 1 then 2 else 1) = 1
  rw [if_neg (by omega)]

/-- Scaling: a bound `4e < x D` with `β D = e` gives `4β < x`. -/
theorem four_beta_lt {β x D e : ℚ} (hD : 0 < D) (hβ : β * D = e) (h : 4 * e < x * D) : 4 * β < x := by
  by_contra hc
  push Not at hc
  nlinarith [mul_le_mul_of_nonneg_right hc hD.le]

/-- **The box `[0, β]²` of the flag-false even child is owned by `Q` at `0`.** -/
theorem F1_box (d n e r : ℤ) (hd : 3 ≤ d) (hn : 1 ≤ n) (hnd : n < d) (hr : 1 ≤ r) (hre : r < e)
    (hdet : d * r - n * e = 1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v β : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * (d : ℚ) + e) + v * ((2 * (n : ℚ) + r) - (2 * (d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * (n : ℚ) + r) + v * ((2 * (d : ℚ) + e) + (2 * (n : ℚ) + r)))
    (hβ : β * (2 * (d : ℚ) + e) = (e : ℚ))
    (hu0 : 0 ≤ u) (hu1 : u ≤ β) (hv0 : 0 ≤ v) (hv1 : v ≤ β) :
    InH ⟨r, e⟩ z := by
  have hdetQ : (d : ℚ) * r - n * e = 1 := by exact_mod_cast hdet
  have hDi : (0 : ℤ) < 2 * d + e := by omega
  have hD : (0 : ℚ) < 2 * (d : ℚ) + e := by exact_mod_cast hDi
  have hmu : muOf ⟨r, e⟩ = 1 := muQ_one r e heven
  have hf : (2 : ℚ) ≤ (e : ℚ) - r := by
    have : (2 : ℤ) ≤ e - r := by omega
    exact_mod_cast this
  obtain ⟨G, hG⟩ : ∃ G : ℚ, G = 2 * (((d : ℚ) + n) * e + ((d : ℚ) - n) * r) + ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) :=
    ⟨_, rfl⟩
  have hK : (0 : ℚ) < ((d : ℚ) + n) * e + ((d : ℚ) - n) * r := by
    have h1 : (0 : ℚ) < (d : ℚ) + n := by exact_mod_cast (show (0 : ℤ) < d + n by omega)
    have h2 : (0 : ℚ) < (d : ℚ) - n := by exact_mod_cast (show (0 : ℤ) < d - n by omega)
    have h3 : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℤ) < e by omega)
    have h4 : (0 : ℚ) < r := by exact_mod_cast (show (0 : ℤ) < r by omega)
    nlinarith [mul_pos h1 h3, mul_pos h2 h4]
  have hT : (0 : ℚ) < (e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2 := by
    have h3 : (0 : ℚ) < e := by exact_mod_cast (show (0 : ℤ) < e by omega)
    have h4 : (0 : ℚ) < r := by exact_mod_cast (show (0 : ℤ) < r by omega)
    have hre' : (r : ℚ) < e := by exact_mod_cast hre
    nlinarith [mul_pos h3 h4]
  have hG0 : 0 ≤ G := by rw [hG]; linarith
  -- the two real identities of the box (exact, using the determinant)
  have ht : (r : ℚ) * z.1 - e * z.2 = ((e : ℚ) + r) / 2 + 2 * u - G * v := by
    rw [hG]
    linear_combination (r : ℚ) * hz1 - (e : ℚ) * hz2 + 2 * u * hdetQ
  have hs : ((e : ℚ) + r) * z.1 + ((e : ℚ) - r) * z.2 = r + G * u - 4 * v := by
    rw [hG]
    linear_combination ((e : ℚ) + r) * hz1 + ((e : ℚ) - r) * hz2 + (-4 * v) * hdetQ
  -- the box bound `G β ≤ T`, from `G e = T D − 2(e − r)`
  have hGe : G * e = ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) * (2 * d + e) - 2 * ((e : ℚ) - r) := by
    rw [hG]
    linear_combination (-2 * ((e : ℚ) - r)) * hdetQ
  have hGβ : G * β ≤ (e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2 := by
    apply le_of_mul_le_mul_right _ hD
    have h1 : G * β * (2 * d + e) = G * e := by linear_combination G * hβ
    rw [h1, hGe]
    linarith
  have hβ1 : β < 1 := by
    apply lt_of_mul_lt_mul_right _ hD.le
    rw [hβ]
    have : (0 : ℚ) < d := by exact_mod_cast (show (0 : ℤ) < d by omega)
    linarith
  -- strict bounds from the polynomial inequalities
  have hB : 4 * β < (r : ℚ) + 1 := by
    have hq : (4 : ℚ) * e < ((r : ℚ) + 1) * (2 * d + e) := by
      exact_mod_cast B_ineq d n e r (by omega) (by omega) hnd hr hre hdet
    exact four_beta_lt hD hβ hq
  -- real bounds on `t` and `s`
  have hGv : G * v ≤ G * β := mul_le_mul_of_nonneg_left hv1 hG0
  have hGu : G * u ≤ G * β := mul_le_mul_of_nonneg_left hu1 hG0
  have hGu0 : 0 ≤ G * u := mul_nonneg hG0 hu0
  have hGv0 : 0 ≤ G * v := mul_nonneg hG0 hv0
  have hLoT : ((e : ℚ) + r) / 2 - (e ^ 2 + 2 * e * r - (r : ℚ) ^ 2) ≤ (r : ℚ) * z.1 - e * z.2 := by
    rw [ht]; linarith
  have hHiT : (r : ℚ) * z.1 - e * z.2 ≤ ((e : ℚ) + r) / 2 + 2 * β := by
    rw [ht]; linarith
  have hLoS : (r : ℚ) - 4 * β ≤ ((e : ℚ) + r) * z.1 + ((e : ℚ) - r) * z.2 := by
    rw [hs]; linarith
  have hHiS : ((e : ℚ) + r) * z.1 + ((e : ℚ) - r) * z.2 ≤ r + (e ^ 2 + 2 * e * r - (r : ℚ) ^ 2) := by
    rw [hs]; linarith
  -- the integer forms of the four `Q`-window facets, in each parity class
  rcases Int.emod_two_eq_zero_or_one (z.1 + z.2) with hpar | hpar
  · -- even sites: `a = min(2r, e − r)`, `l = 0`
    have hev : decide ((z.1 + z.2) % 2 = 0) = true := decide_eq_true hpar
    rw [inH_Q_iff r e z true hev hmu]
    have hA : aOf ⟨r, e⟩ true = min (2 * r) (e - r) := by simp [aOf]
    have hl : lOf ⟨r, e⟩ true = 0 := by simp [lOf]
    rw [hA, hl]
    have hS0 : (-1 : ℚ) < ((e : ℚ) + r) * z.1 + ((e : ℚ) - r) * z.2 := by linarith [hLoS, hB]
    have hS0' : (0 : ℤ) ≤ (e + r) * z.1 + (e - r) * z.2 := by
      have h : ((-1 : ℤ) : ℚ) < (((e + r) * z.1 + (e - r) * z.2 : ℤ) : ℚ) := by push_cast; exact hS0
      have h' := Int.cast_lt.mp h
      have := Int.lt_iff_add_one_le.mp h'
      linarith
    have hr0 : (0 : ℚ) ≤ r := by exact_mod_cast (show (0 : ℤ) ≤ r by omega)
    have hSup : (e + r) * z.1 + (e - r) * z.2 ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 := by
      have h : (((e + r) * z.1 + (e - r) * z.2 : ℤ) : ℚ) ≤ (((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - 0 : ℤ)) : ℚ) := by
        push_cast; linarith [hHiS, hr0]
      exact_mod_cast h
    rcases le_total (2 * r) (e - r) with hm | hm
    · -- `e ≥ 3r`, the minimum is `2r`
      rw [min_eq_left hm]
      have hmq : (2 * (r : ℚ)) ≤ e - r := by exact_mod_cast hm
      have hC2 : (4 : ℚ) * β < e - 3 * r + 2 := by
        have hq : (4 : ℚ) * e < ((e : ℚ) - 3 * r + 2) * (2 * d + e) := by
          exact_mod_cast C2_ineq d n e r (by omega) (by omega) hr hre hdet (by omega)
        exact four_beta_lt hD hβ hq
      refine ⟨?_, ?_, hS0', hSup⟩
      · have h : ((2 * r - (e ^ 2 + 2 * e * r - r ^ 2) : ℤ) : ℚ) ≤ ((r * z.1 - e * z.2 : ℤ) : ℚ) := by
          push_cast; linarith [hLoT, hmq]
        exact_mod_cast h
      · have h : ((r * z.1 - e * z.2 : ℤ) : ℚ) < ((e - r + 1 : ℤ) : ℚ) := by
          push_cast; linarith [hHiT, hC2]
        have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
        linarith
    · -- `e ≤ 3r`, the minimum is `e − r`
      rw [min_eq_right hm]
      have hmq : (e : ℚ) - r ≤ 2 * r := by exact_mod_cast hm
      have hC1 : (4 : ℚ) * β < 3 * r - e + 2 := by
        have hq : (4 : ℚ) * e < (3 * (r : ℚ) - e + 2) * (2 * d + e) := by
          exact_mod_cast C1_ineq d n e r (by omega) (by omega) hr hre hdet hodd (by omega)
        exact four_beta_lt hD hβ hq
      refine ⟨?_, ?_, hS0', ?_⟩
      · have h : ((e - r - (e ^ 2 + 2 * e * r - r ^ 2) : ℤ) : ℚ) ≤ ((r * z.1 - e * z.2 : ℤ) : ℚ) := by
          push_cast; linarith [hLoT]
        exact_mod_cast h
      · have h : ((r * z.1 - e * z.2 : ℤ) : ℚ) < ((2 * r + 1 : ℤ) : ℚ) := by
          push_cast; linarith [hHiT, hC1]
        have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
        linarith
      · exact hSup
  · -- odd sites: `a = r`, `l = min(e − r, 3r − e)`
    have hev : decide ((z.1 + z.2) % 2 = 0) = false := decide_eq_false (by omega)
    rw [inH_Q_iff r e z false hev hmu]
    have hA : aOf ⟨r, e⟩ false = r := by simp [aOf]
    have hl : lOf ⟨r, e⟩ false = min (e - r) (3 * r - e) := by simp [lOf]
    rw [hA, hl]
    have hreq : (r : ℚ) < e := by exact_mod_cast hre
    have hT0 : (r - (e ^ 2 + 2 * e * r - r ^ 2) : ℤ) ≤ r * z.1 - e * z.2 := by
      have h : ((r - (e ^ 2 + 2 * e * r - r ^ 2) : ℤ) : ℚ) ≤ ((r * z.1 - e * z.2 : ℤ) : ℚ) := by
        push_cast; linarith [hLoT]
      exact_mod_cast h
    have hT1 : r * z.1 - e * z.2 ≤ e + r - r := by
      have h : ((r * z.1 - e * z.2 : ℤ) : ℚ) < ((e + 1 : ℤ) : ℚ) := by
        push_cast; linarith [hHiT, hβ1, hf]
      have h' := Int.lt_add_one_iff.mp (Int.cast_lt.mp h)
      linarith
    have hSupO : (e + r) * z.1 + (e - r) * z.2 ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - min (e - r) (3 * r - e) := by
      rcases le_total e (2 * r) with hle | hle
      · rw [min_eq_left (show e - r ≤ 3 * r - e by omega)]
        have h : (((e + r) * z.1 + (e - r) * z.2 : ℤ) : ℚ) ≤ ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (e - r) : ℤ) : ℚ) := by
          have hle' : (e : ℚ) ≤ 2 * r := by exact_mod_cast hle
          push_cast; linarith [hHiS, hle']
        exact_mod_cast h
      · rw [min_eq_right (show 3 * r - e ≤ e - r by omega)]
        have h : (((e + r) * z.1 + (e - r) * z.2 : ℤ) : ℚ) ≤ ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - (3 * r - e) : ℤ) : ℚ) := by
          have hle' : (2 * (r : ℚ)) ≤ e := by exact_mod_cast hle
          push_cast; linarith [hHiS, hle']
        exact_mod_cast h
    rcases le_total e (2 * r) with hle | hle
    · rw [min_eq_left (show e - r ≤ 3 * r - e by omega)] at hSupO ⊢
      have hq : (4 : ℚ) * e < (2 * (r : ℚ) + 1 - e) * (2 * d + e) := by
        exact_mod_cast A1_ineq d n e r (by omega) (by omega) (by omega) hre hdet heven hle
      have hA1r : 4 * β < 2 * (r : ℚ) + 1 - e := four_beta_lt hD hβ hq
      refine ⟨hT0, hT1, ?_, hSupO⟩
      have h : (((e - r - 1 : ℤ)) : ℚ) < ((((e + r) * z.1 + (e - r) * z.2 : ℤ)) : ℚ) := by
        push_cast; linarith [hLoS, hA1r]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith
    · rw [min_eq_right (show 3 * r - e ≤ e - r by omega)] at hSupO ⊢
      have hq : (4 : ℚ) * e < ((e : ℚ) + 1 - 2 * r) * (2 * d + e) := by
        exact_mod_cast A2_ineq d n e r (by omega) (by omega) (by omega) hre hdet heven (by omega)
      have hA2r : 4 * β < (e : ℚ) + 1 - 2 * r := four_beta_lt hD hβ hq
      refine ⟨hT0, hT1, ?_, hSupO⟩
      have h : (((3 * r - e - 1 : ℤ)) : ℚ) < ((((e + r) * z.1 + (e - r) * z.2 : ℤ)) : ℚ) := by
        push_cast; linarith [hLoS, hA2r]
      have h' := Int.lt_iff_add_one_le.mp (Int.cast_lt.mp h)
      linarith

end FLatticePaper.Tiles.PairEvenW0Q
