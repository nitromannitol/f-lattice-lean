import FLatticePaper.Tiles.PairBoxesP0Even
import FLatticePaper.Tiles.SiteInduction

/-! Task 53, item 2 (covering reduction), section 6: the integer assembly on the box of the odd parent `P` at zero offset.

Flag-true odd child (`δ = dr − ne = −1`, `P = (d, n)` odd, `Q = (e, r)` even), with `X = P + Q`. The cell point of an integer
`z` is `z − B0 = u U + v V`, `U = (2(d+e), 2(n+r))`, `V = (n+r−(d+e), d+e+n+r)`. On the box `0 ≤ u, v ≤ α`, `α = d/(d+e)`,
the integer point `z` lies in `HSet P` (`InH P z`), which is the first source of `oddChildS`.

* `t_cell`, `s_cell`: the integer coordinates `t = n z₁ − d z₂`, `s = (d+n) z₁ + (d−n) z₂` in terms of `u, v`.
* `inH_odd`: odd sites, from the four odd box bounds and the integer mesh slack.
* `inH_even_of_top`: even sites, from the even box bounds, with the upper `t` bound supplied as `htop`.
* `top_gen`: the upper `t` bound at even sites when `(e, r) ≠ (3, 1)`, from `t_upper_even`.
* `top_31`: the same bound for `(e, r) = (3, 1)`, where `t_upper_even` is not available. The real bound gives `t ≤ 2n + 1`;
  the value `t = 2n + 1` is excluded by integrality: `N_v = 2T_X v` is odd, so `N_v ≥ 1`, which puts `u` above `α`.
* `inH_box0`: an integer point of the box lies in `HSet P`. -/

namespace FLatticePaper.Tiles.PairOwnerP0

open FLatticePaper.Tiles.SiteInduction
open FLatticePaper.Tiles.PairBoxesP0 FLatticePaper.Tiles.PairBoxesP0Even

/-- The coordinate `t_P(z) = n z₁ − d z₂` of an integer point of the cell, in the box variables. -/
theorem t_cell (d n e r : ℤ) (hdet : d * r - n * e = -1) (z : ℤ × ℤ) (t : ℤ) (ht : t = n * z.1 - d * z.2) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r))) :
    (t : ℚ) = ((d : ℚ) + n) / 2 + 2 * u -
      (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * v := by
  have hdetQ : (d : ℚ) * r - n * e = -1 := by exact_mod_cast hdet
  subst ht
  push_cast
  linear_combination (n : ℚ) * hz1 - (d : ℚ) * hz2 - 2 * u * hdetQ

/-- The coordinate `s_P(z) = (d + n) z₁ + (d − n) z₂` of an integer point of the cell, in the box variables. -/
theorem s_cell (d n e r : ℤ) (hdet : d * r - n * e = -1) (z : ℤ × ℤ) (s : ℤ) (hs : s = (d + n) * z.1 + (d - n) * z.2)
    (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r))) :
    (s : ℚ) = (n : ℚ) + 2 * (((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + ((d + n) * e + (d - n) * r : ℚ)) * u - 2 * v := by
  have hdetQ : (d : ℚ) * r - n * e = -1 := by exact_mod_cast hdet
  subst hs
  push_cast
  linear_combination ((d : ℚ) + n) * hz1 + ((d : ℚ) - n) * hz2 + 2 * v * hdetQ

/-- Odd sites: an integer point of the box with odd parity lies in `HSet P`. -/
theorem inH_odd (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hu0 : 0 ≤ u) (hu1 : u ≤ (d : ℚ) / (d + e)) (hv0 : 0 ≤ v) (hv1 : v ≤ (d : ℚ) / (d + e))
    (hpar : (z.1 + z.2) % 2 = 1) : InH ⟨n, d⟩ z := by
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = n * z.1 - d * z.2 := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s : ℤ, s = (d + n) * z.1 + (d - n) * z.2 := ⟨_, rfl⟩
  have ht' := t_cell d n e r hdet z t ht u v hz1 hz2
  have hs' := s_cell d n e r hdet z s hs u v hz1 hz2
  have h1 := t_lower_odd d n e r hn hnd hr hre hdet u v hu0 hv0 hv1
  have h2 := t_upper_odd d n e r hn hnd hr hre heven hodd hdet u v hu0 hu1 hv0 hv1
  have h3 := s_lower_odd d n e r hn hnd hr hre hdet u v hu0 hv0 hv1 heven
  have h4 := s_upper_odd d n e r hn hnd hr hre hdet u v hu0 hu1 hv0
  have hT1 : n - (d ^ 2 + 2 * d * n - n ^ 2) - 1 < t := by
    have : (n : ℚ) - ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) - 1 < (t : ℚ) := by rw [ht']; linarith
    exact_mod_cast this
  have hT2 : t < d + 1 := by
    have : (t : ℚ) < (d : ℚ) + 1 := by rw [ht']; linarith
    exact_mod_cast this
  have hS1 : min (d - n) (3 * n - d) - 1 < s := by
    have : ((min (d - n) (3 * n - d) : ℤ) : ℚ) - 1 < (s : ℚ) := by rw [hs']; linarith
    exact_mod_cast this
  have hS2 : s < 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - min (d - n) (3 * n - d) + 1 := by
    have : (s : ℚ) < 2 * ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + 2 * n - ((min (d - n) (3 * n - d) : ℤ) : ℚ) + 1 := by
      rw [hs']; linarith
    exact_mod_cast this
  have hmu : muOf ⟨n, d⟩ = 2 := by
    have hnd2 : (n + d) % 2 = 1 := by omega
    show (if (n + d) % 2 = 1 then 2 else 1) = 2
    rw [if_pos hnd2]
  have hdec : decide ((z.1 + z.2) % 2 = 0) = false := by
    rw [decide_eq_false_iff_not]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdec]
    show n - (d ^ 2 + 2 * d * n - n ^ 2) ≤ n * z.1 - d * z.2
    rw [← ht]; linarith
  · rw [hdec]
    show n * z.1 - d * z.2 ≤ d + n - n
    rw [← ht]; linarith
  · rw [hdec]
    show min (d - n) (3 * n - d) ≤ (d + n) * z.1 + (d - n) * z.2
    rw [← hs]; linarith
  · rw [hdec, hmu]
    show (d + n) * z.1 + (d - n) * z.2 ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - min (d - n) (3 * n - d)
    rw [← hs]; linarith

/-- Even sites: the four even window bounds, with the upper `t` bound `htop` supplied. -/
theorem inH_even_of_top (d n e r t : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1)
    (z : ℤ × ℤ) (ht : t = n * z.1 - d * z.2) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hu0 : 0 ≤ u) (hu1 : u ≤ (d : ℚ) / (d + e)) (hv0 : 0 ≤ v) (hv1 : v ≤ (d : ℚ) / (d + e))
    (hpar : (z.1 + z.2) % 2 = 0) (htop : t ≤ d + n - min (2 * n) (d - n)) : InH ⟨n, d⟩ z := by
  obtain ⟨s, hs⟩ : ∃ s : ℤ, s = (d + n) * z.1 + (d - n) * z.2 := ⟨_, rfl⟩
  have ht' := t_cell d n e r hdet z t ht u v hz1 hz2
  have hs' := s_cell d n e r hdet z s hs u v hz1 hz2
  obtain ⟨m, hm⟩ : ∃ m : ℤ, m = min (2 * n) (d - n) := ⟨_, rfl⟩
  have h1 := t_lower_even d n e r m hn hnd hr hre hdet hm u v hu0 hv1
  have h3 := s_lower_even d n e r hn hnd hr hre u v hu0 hv1
  have h4 := s_upper_even d n e r hn hnd hr hre hdet u v hu1 hv0
  have hT1 : m - (d ^ 2 + 2 * d * n - n ^ 2) - 1 < t := by
    have : (m : ℚ) - ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) - 1 < (t : ℚ) := by rw [ht']; linarith
    exact_mod_cast this
  have hS1 : (0 : ℤ) - 1 < s := by
    have : (0 : ℚ) - 1 < (s : ℚ) := by rw [hs']; linarith
    exact_mod_cast this
  have hS2 : s < 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n + 1 := by
    have : (s : ℚ) < 2 * ((d : ℚ) ^ 2 + 2 * d * n - n ^ 2) + 2 * n + 1 := by rw [hs']; linarith
    exact_mod_cast this
  have hmu : muOf ⟨n, d⟩ = 2 := by
    have hnd2 : (n + d) % 2 = 1 := by omega
    show (if (n + d) % 2 = 1 then 2 else 1) = 2
    rw [if_pos hnd2]
  have hdec : decide ((z.1 + z.2) % 2 = 0) = true := by
    rw [decide_eq_true_iff]; exact hpar
  rw [← hm] at htop
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdec]
    show min (2 * n) (d - n) - (d ^ 2 + 2 * d * n - n ^ 2) ≤ n * z.1 - d * z.2
    rw [← ht, ← hm]; linarith
  · rw [hdec]
    show n * z.1 - d * z.2 ≤ d + n - min (2 * n) (d - n)
    rw [← ht]; linarith
  · rw [hdec]
    show 0 ≤ (d + n) * z.1 + (d - n) * z.2
    rw [← hs]; linarith
  · rw [hdec, hmu]
    show (d + n) * z.1 + (d - n) * z.2 ≤ 2 * (d ^ 2 + 2 * d * n - n ^ 2) + 2 * n - 0
    rw [← hs]; linarith

/-- The upper `t` bound at even sites for `(e, r) ≠ (3, 1)`, from the real box bound of `PairBoxesP0Even`. -/
theorem top_gen (d n e r t : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (hnot : ¬ (e = 3 ∧ r = 1))
    (z : ℤ × ℤ) (ht : t = n * z.1 - d * z.2) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hu0 : 0 ≤ u) (hu1 : u ≤ (d : ℚ) / (d + e)) (hv0 : 0 ≤ v) :
    t ≤ d + n - min (2 * n) (d - n) := by
  have ht' := t_cell d n e r hdet z t ht u v hz1 hz2
  have h := t_upper_even d n e r (min (2 * n) (d - n)) hn hnd hr hre hdet hodd hnot rfl u v hu0 hu1 hv0
  have : (t : ℚ) < (d : ℚ) + n - ((min (2 * n) (d - n) : ℤ) : ℚ) + 1 := by rw [ht']; linarith
  have h2 : t < d + n - min (2 * n) (d - n) + 1 := by exact_mod_cast this
  omega

/-- The upper `t` bound at even sites for `(e, r) = (3, 1)`, where `d = 3n − 1`. The real bound gives `t ≤ 2n + 1`; the value
`2n + 1` is excluded by integrality (the box does not contain it). -/
theorem top_31 (d n e r t : ℤ) (he : e = 3) (hr1 : r = 1) (hn : 1 ≤ n) (hdet : d * r - n * e = -1)
    (z : ℤ × ℤ) (ht : t = n * z.1 - d * z.2) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hu0 : 0 ≤ u) (hu1 : u ≤ (d : ℚ) / (d + e)) (hv0 : 0 ≤ v) :
    t ≤ d + n - min (2 * n) (d - n) := by
  have hd : d = 3 * n - 1 := by subst he hr1; omega
  have hpos : (0 : ℚ) < (d : ℚ) + e := by
    have : (0 : ℤ) < d + e := by omega
    exact_mod_cast this
  have hub : u * ((d : ℚ) + e) ≤ d := (le_div_iff₀ hpos).mp hu1
  have ht' := t_cell d n e r hdet z t ht u v hz1 hz2
  subst he hr1 hd
  push_cast at ht' hub hz1 hz2 ⊢
  have ht2 : (t : ℚ) = (4 * n - 1) / 2 + 2 * u - (14 * n ^ 2 + 6 * n - 3) * v := by
    rw [ht']; ring
  have hc0 : (0 : ℚ) ≤ 14 * n ^ 2 + 6 * n - 3 := by
    have : (1 : ℚ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hu_lt : u < 1 := by
    have : (3 : ℚ) * n - 1 + 3 > 0 := by
      have : (1 : ℚ) ≤ n := by exact_mod_cast hn
      linarith
    nlinarith
  have hup : (t : ℚ) < 2 * n + 2 := by
    rw [ht2]; nlinarith [mul_nonneg hc0 hv0]
  have htle : t ≤ 2 * n + 1 := by
    have : t < 2 * n + 2 := by exact_mod_cast hup
    omega
  rw [show min (2 * n) (3 * n - 1 - n) = 2 * n - 1 by omega]
  by_contra hcon
  have htv : t = 2 * n + 1 := by omega
  -- the exceptional row: `2u − c v = 3/2`
  have hcv : 2 * u - (14 * n ^ 2 + 6 * n - 3) * v = 3 / 2 := by
    have : (t : ℚ) = 2 * n + 1 := by exact_mod_cast htv
    linarith
  obtain ⟨Nu, hNu⟩ : ∃ N : ℤ, N = (4 * n + 3) * z.1 + (2 * n + 1) * z.2 - n - 1 := ⟨_, rfl⟩
  obtain ⟨Nv, hNv⟩ : ∃ N : ℤ, N = (6 * n + 4) * z.2 - (2 * n + 2) * z.1 + 4 * n + 3 := ⟨_, rfl⟩
  have hNu' : (Nu : ℚ) = 2 * (14 * (n : ℚ) ^ 2 + 20 * n + 7) * u := by
    rw [hNu]; push_cast
    linear_combination (4 * (n : ℚ) + 3) * hz1 + (2 * (n : ℚ) + 1) * hz2
  have hNv' : (Nv : ℚ) = 2 * (14 * (n : ℚ) ^ 2 + 20 * n + 7) * v := by
    rw [hNv]; push_cast
    linear_combination (6 * (n : ℚ) + 4) * hz2 - (2 * (n : ℚ) + 2) * hz1
  have hq : ((2 * Nu - (14 * n ^ 2 + 6 * n - 3) * Nv : ℤ) : ℚ) = ((3 * (14 * n ^ 2 + 20 * n + 7) : ℤ) : ℚ) := by
    push_cast
    linear_combination 2 * hNu' - (14 * (n : ℚ) ^ 2 + 6 * n - 3) * hNv' + 2 * (14 * (n : ℚ) ^ 2 + 20 * n + 7) * hcv
  have hint : 2 * Nu - (14 * n ^ 2 + 6 * n - 3) * Nv = 3 * (14 * n ^ 2 + 20 * n + 7) := by
    exact_mod_cast hq
  -- parity: `Nv` is odd, because `14 n² + 6n − 3` and `3(14 n² + 20 n + 7)` are odd
  obtain ⟨X, hX⟩ : ∃ X : ℤ, X = (14 * n ^ 2 + 6 * n - 3) * Nv := ⟨_, rfl⟩
  rw [← hX] at hint
  have hc2 : (14 * n ^ 2 + 6 * n - 3 : ℤ) % 2 = 1 := by
    have : (14 * n ^ 2 + 6 * n - 3 : ℤ) = 2 * (7 * n ^ 2 + 3 * n - 2) + 1 := by ring
    omega
  have hTX2 : (3 * (14 * n ^ 2 + 20 * n + 7) : ℤ) % 2 = 1 := by
    have : (3 * (14 * n ^ 2 + 20 * n + 7) : ℤ) = 2 * (21 * n ^ 2 + 30 * n + 10) + 1 := by ring
    omega
  have hmod : X % 2 = Nv % 2 := by
    rw [hX, Int.mul_emod, hc2]; simp
  have hNv_odd : Nv % 2 = 1 := by omega
  have hNv0 : 0 ≤ Nv := by
    have : (0 : ℚ) ≤ Nv := by
      rw [hNv']
      have : (0 : ℚ) ≤ 14 * (n : ℚ) ^ 2 + 20 * n + 7 := by
        have : (0 : ℚ) ≤ n := by exact_mod_cast (by omega : (0 : ℤ) ≤ n)
        positivity
      exact mul_nonneg (mul_nonneg (by norm_num) this) hv0
    exact_mod_cast this
  have hNv1 : 1 ≤ Nv := by omega
  have hc0Z : (0 : ℤ) ≤ 14 * n ^ 2 + 6 * n - 3 := by nlinarith
  have hX1 : (14 * n ^ 2 + 6 * n - 3) * 1 ≤ X := by
    rw [hX]; exact mul_le_mul_of_nonneg_left hNv1 hc0Z
  have h2Nu : 3 * (14 * n ^ 2 + 20 * n + 7) + (14 * n ^ 2 + 6 * n - 3) ≤ 2 * Nu := by
    linarith
  -- the box bound `Nu (3n + 2) ≤ 2 T_X (3n − 1)`
  have hbox : Nu * (3 * n + 2) ≤ 2 * (14 * n ^ 2 + 20 * n + 7) * (3 * n - 1) := by
    have hTXnn : (0 : ℚ) ≤ 2 * (14 * (n : ℚ) ^ 2 + 20 * n + 7) := by
      have : (0 : ℚ) ≤ n := by exact_mod_cast (by omega : (0 : ℤ) ≤ n)
      positivity
    have hq2 : ((Nu * (3 * n + 2) : ℤ) : ℚ) ≤ ((2 * (14 * n ^ 2 + 20 * n + 7) * (3 * n - 1) : ℤ) : ℚ) := by
      push_cast
      rw [hNu']
      have := mul_le_mul_of_nonneg_left hub hTXnn
      nlinarith
    exact_mod_cast hq2
  have hprod : (3 * (14 * n ^ 2 + 20 * n + 7) + (14 * n ^ 2 + 6 * n - 3)) * (3 * n + 2) ≤ (2 * Nu) * (3 * n + 2) :=
    mul_le_mul_of_nonneg_right h2Nu (by omega)
  nlinarith [hprod, hbox, sq_nonneg n]

/-- Even sites, the upper bound with the `(3, 1)` family handled by `top_31`. -/
theorem inH_box0_even (d n e r t : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1)
    (z : ℤ × ℤ) (ht : t = n * z.1 - d * z.2) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hu0 : 0 ≤ u) (hu1 : u ≤ (d : ℚ) / (d + e)) (hv0 : 0 ≤ v) (hv1 : v ≤ (d : ℚ) / (d + e))
    (hpar : (z.1 + z.2) % 2 = 0) : InH ⟨n, d⟩ z := by
  have htop : t ≤ d + n - min (2 * n) (d - n) := by
    by_cases hc : e = 3 ∧ r = 1
    · exact top_31 d n e r t hc.1 hc.2 hn hdet z ht u v hz1 hz2 hu0 hu1 hv0
    · exact top_gen d n e r t hn hnd hr hre hdet hodd hc z ht u v hz1 hz2 hu0 hu1 hv0
  exact inH_even_of_top d n e r t hn hnd hr hre hdet hodd z ht u v hz1 hz2 hu0 hu1 hv0 hv1 hpar htop

/-- **The integer assembly on the zero-offset box.** For an integer point `z` of the cell of `X = P + Q` (flag true) with
`(u, v) ∈ [0, α]²`, `z` lies in `HSet P`. -/
theorem inH_box0 (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (hodd : (d + n) % 2 = 1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hu0 : 0 ≤ u) (hu1 : u ≤ (d : ℚ) / (d + e)) (hv0 : 0 ≤ v) (hv1 : v ≤ (d : ℚ) / (d + e)) :
    InH ⟨n, d⟩ z := by
  rcases (show (z.1 + z.2) % 2 = 0 ∨ (z.1 + z.2) % 2 = 1 by omega) with hpar | hpar
  · obtain ⟨t, ht⟩ : ∃ t : ℤ, t = n * z.1 - d * z.2 := ⟨_, rfl⟩
    exact inH_box0_even d n e r t hn hnd hr hre hdet hodd z ht u v hz1 hz2 hu0 hu1 hv0 hv1 hpar
  · exact inH_odd d n e r hn hnd hr hre hdet hodd heven z u v hz1 hz2 hu0 hu1 hv0 hv1 hpar

end FLatticePaper.Tiles.PairOwnerP0
