import FLatticePaper.Tiles.PairQAbox

/-! Task 53, item 2 (covering reduction), section 8: the repeated `Q` cells of the group at `B = V_P` in the flag-true odd child.

The nominal owner is the box `[0, β] × [α, 1]` of `Q` (flag-true, `δ = −1`). The two copies are `Q@V_P` (`z − V_P`) and
`Q@V_P + Q` (`z − V_P − Q`). The split is the midpoint of the `u`-range, `u ≤ β/2` (first copy) and `u ≥ β/2` (second copy);
this was checked numerically on all flag-true pairs with den ≤ 14 (8908 points, no failures).

For `w = z − V_P`: `t_Q(w) = (e+r)/2 + K − 2u − W v`, `s_Q(w) = r − 2 + 2W u + 2v`, where `K = s_Q(P)`, `W = K + T`.
The second copy has the same `t` and `s − T`. The only exceptional facet is the second copy's even lower `t` bound at `e = 3r`,
which needs `e < d`; the leftover `(d, n, e, r) = (2, 1, 3, 1)` is handled by `82 v < 82`. -/

namespace FLatticePaper.Tiles.PairQBBox

open FLatticePaper.Tiles.SiteInduction FLatticePaper.Tiles.PairQAbox

/-- The `t_Q` of `z − V_P` in terms of `(u, v)`. -/
theorem t_formula_QB (d n e r : ℤ) (hdet : d * r - n * e = -1) (z : ℤ × ℤ) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r))) :
    (r : ℚ) * ((z.1 : ℚ) - (n - d)) - (e : ℚ) * ((z.2 : ℚ) - (n + d)) =
      ((e : ℚ) + r) / 2 + Kq d n e r - 2 * u - (Kq d n e r + Tq e r) * v := by
  have hdetQ : (d : ℚ) * r - n * e = -1 := by exact_mod_cast hdet
  unfold Kq Tq
  linear_combination (r : ℚ) * hz1 - (e : ℚ) * hz2 + 2 * u * hdetQ

/-- The `s_Q` of `z − V_P` in terms of `(u, v)`. -/
theorem s_formula_QB (d n e r : ℤ) (hdet : d * r - n * e = -1) (z : ℤ × ℤ) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r))) :
    ((e : ℚ) + r) * ((z.1 : ℚ) - (n - d)) + ((e : ℚ) - r) * ((z.2 : ℚ) - (n + d)) =
      r - 2 + 2 * (Kq d n e r + Tq e r) * u + 2 * v := by
  have hdetQ : (d : ℚ) * r - n * e = -1 := by exact_mod_cast hdet
  unfold Kq Tq
  linear_combination ((e : ℚ) + r) * hz1 + ((e : ℚ) - r) * hz2 + (2 - 2 * v) * hdetQ

/-- Real facets of the first copy on `[0, β/2] × [α, 1]`. -/
theorem QB_real1 (E R K T α β κ u v : ℚ) (hW : 0 ≤ K + T) (hαβ : α + β = 1) (hK : β * K - α * T = κ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ β / 2) (hv0 : α ≤ v) (hv1 : v ≤ 1) :
    (E + R) / 2 + K - 2 * u - (K + T) * v ≤ (E + R) / 2 + κ ∧
    (E + R) / 2 - T - β ≤ (E + R) / 2 + K - 2 * u - (K + T) * v ∧
    R - 2 + 2 * α ≤ R - 2 + 2 * (K + T) * u + 2 * v ∧
    R - 2 + 2 * (K + T) * u + 2 * v ≤ T + R + κ := by
  have hWβ : (K + T) * β = T + κ := by linear_combination hK + T * hαβ
  have hWα : (K + T) * α = K - κ := by linear_combination -hK + K * hαβ
  have hWu0 : 0 ≤ (K + T) * u := mul_nonneg hW hu0
  have hWv1 : (K + T) * α ≤ (K + T) * v := mul_le_mul_of_nonneg_left hv0 hW
  have hWv2 : (K + T) * v ≤ (K + T) * 1 := mul_le_mul_of_nonneg_left hv1 hW
  have hWu1 : (K + T) * u ≤ (K + T) * (β / 2) := mul_le_mul_of_nonneg_left hu1 hW
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Real facets of the second copy on `[β/2, β] × [α, 1]`; the shifted `s` is `s − T`. -/
theorem QB_real2 (E R K T α β κ u v : ℚ) (hW : 0 ≤ K + T) (hαβ : α + β = 1) (hK : β * K - α * T = κ)
    (hu0 : β / 2 ≤ u) (hu1 : u ≤ β) (hv0 : α ≤ v) (hv1 : v ≤ 1) :
    (E + R) / 2 + K - 2 * u - (K + T) * v ≤ (E + R) / 2 - β + κ ∧
    (E + R) / 2 - T - 2 * β ≤ (E + R) / 2 + K - 2 * u - (K + T) * v ∧
    R - 2 + κ + 2 * α ≤ R - 2 + 2 * (K + T) * u + 2 * v - T ∧
    R - 2 + 2 * (K + T) * u + 2 * v - T ≤ R + T + 2 * κ := by
  have hWβ : (K + T) * β = T + κ := by linear_combination hK + T * hαβ
  have hWα : (K + T) * α = K - κ := by linear_combination -hK + K * hαβ
  have hWu0 : (K + T) * (β / 2) ≤ (K + T) * u := mul_le_mul_of_nonneg_left hu0 hW
  have hWu1 : (K + T) * u ≤ (K + T) * β := mul_le_mul_of_nonneg_left hu1 hW
  have hWv1 : (K + T) * α ≤ (K + T) * v := mul_le_mul_of_nonneg_left hv0 hW
  have hWv2 : (K + T) * v ≤ (K + T) * 1 := mul_le_mul_of_nonneg_left hv1 hW
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Odd sites, first copy `Q@V_P`. -/
theorem inH_QB1_odd (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu0 : 0 ≤ u) (hu1 : u ≤ β / 2) (hv0 : α ≤ v) (hv1 : v ≤ 1)
    (hpar : (z.1 + z.2) % 2 = 1) :
    InH ⟨r, e⟩ (z.1 - (n - d), z.2 - (n + d)) := by
  obtain ⟨hαpos, hαlt, hβpos, hβlt, hκpos, hκlt, hW, h1, hK⟩ :=
    box_facts d n e r hn hnd hr hre hdet α β κ hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := QB_real1 (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW h1 hK hu0 hu1 hv0 hv1
  have ht := t_formula_QB d n e r hdet z u v hz1 hz2
  have hs := s_formula_QB d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R1 R2 R3 R4 ht hs
  have hE2 : (2 : ℚ) ≤ (e : ℚ) - r := by
    have h : (2 : ℤ) ≤ e - r := by omega
    exact_mod_cast h
  have hne := e_ne_two_r d n e r hr hdet heven
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = min (e - r) (3 * r - e) := ⟨_, rfl⟩
  have hLle : L ≤ r - 1 := by omega
  have hLq : (L : ℚ) ≤ (r : ℚ) - 1 := by exact_mod_cast hLle
  have hev : decide ((z.1 - (n - d) + (z.2 - (n + d))) % 2 = 0) = false := by
    rw [decide_eq_false_iff_not]; omega
  have hmu : muOf ⟨r, e⟩ = 1 := by
    show (if (r + e) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  rw [inH_Q_iff r e _ false hev hmu]
  have hA : aOf ⟨r, e⟩ false = r := rfl
  have hl : lOf ⟨r, e⟩ false = L := by rw [hL]; rfl
  rw [hA, hl]
  dsimp only
  have A1 : r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * (z.1 - (n - d)) - e * (z.2 - (n + d)) := by
    have h : ((r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) < ((r * (z.1 - (n - d)) - e * (z.2 - (n + d)) : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith
    exact_mod_cast h
  have A2 : r * (z.1 - (n - d)) - e * (z.2 - (n + d)) < e + 1 := by
    have h : ((r * (z.1 - (n - d)) - e * (z.2 - (n + d)) : ℤ) : ℚ) < ((e + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith
    exact_mod_cast h
  have A3 : L - 1 < (e + r) * (z.1 - (n - d)) + (e - r) * (z.2 - (n + d)) := by
    have h : ((L - 1 : ℤ) : ℚ) < (((e + r) * (z.1 - (n - d)) + (e - r) * (z.2 - (n + d)) : ℤ) : ℚ) := by
      push_cast; rw [hs]; linarith
    exact_mod_cast h
  have A4 : (e + r) * (z.1 - (n - d)) + (e - r) * (z.2 - (n + d)) < 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - L + 1 := by
    have h : (((e + r) * (z.1 - (n - d)) + (e - r) * (z.2 - (n + d)) : ℤ) : ℚ) <
        ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - L + 1 : ℤ) : ℚ) := by
      push_cast; rw [hs]; linarith
    exact_mod_cast h
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Odd sites, second copy `Q@V_P + Q`. -/
theorem inH_QB2_odd (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu0 : β / 2 ≤ u) (hu1 : u ≤ β) (hv0 : α ≤ v) (hv1 : v ≤ 1)
    (hpar : (z.1 + z.2) % 2 = 1) :
    InH ⟨r, e⟩ (z.1 - (n - d) - e, z.2 - (n + d) - r) := by
  obtain ⟨hαpos, hαlt, hβpos, hβlt, hκpos, hκlt, hW, h1, hK⟩ :=
    box_facts d n e r hn hnd hr hre hdet α β κ hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := QB_real2 (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW h1 hK hu0 hu1 hv0 hv1
  have ht := t_formula_QB d n e r hdet z u v hz1 hz2
  have hs := s_formula_QB d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R1 R2 R3 R4 ht hs
  have ht' : (r : ℚ) * ((z.1 : ℚ) - (n - d) - e) - (e : ℚ) * ((z.2 : ℚ) - (n + d) - r) =
      (r : ℚ) * ((z.1 : ℚ) - (n - d)) - (e : ℚ) * ((z.2 : ℚ) - (n + d)) := by ring
  have hs' : ((e : ℚ) + r) * ((z.1 : ℚ) - (n - d) - e) + ((e : ℚ) - r) * ((z.2 : ℚ) - (n + d) - r) =
      ((e : ℚ) + r) * ((z.1 : ℚ) - (n - d)) + ((e : ℚ) - r) * ((z.2 : ℚ) - (n + d)) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) := by
    ring
  have hE2 : (2 : ℚ) ≤ (e : ℚ) - r := by
    have h : (2 : ℤ) ≤ e - r := by omega
    exact_mod_cast h
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = min (e - r) (3 * r - e) := ⟨_, rfl⟩
  have hLle : L ≤ r - 1 := by
    have hne := e_ne_two_r d n e r hr hdet heven
    omega
  have hLq : (L : ℚ) ≤ (r : ℚ) - 1 := by exact_mod_cast hLle
  have hev : decide ((z.1 - (n - d) - e + (z.2 - (n + d) - r)) % 2 = 0) = false := by
    rw [decide_eq_false_iff_not]; omega
  have hmu : muOf ⟨r, e⟩ = 1 := by
    show (if (r + e) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  rw [inH_Q_iff r e _ false hev hmu]
  have hA : aOf ⟨r, e⟩ false = r := rfl
  have hl : lOf ⟨r, e⟩ false = L := by rw [hL]; rfl
  rw [hA, hl]
  dsimp only
  have B1 : r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * (z.1 - (n - d) - e) - e * (z.2 - (n + d) - r) := by
    have h : ((r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) <
        ((r * (z.1 - (n - d) - e) - e * (z.2 - (n + d) - r) : ℤ) : ℚ) := by
      push_cast; rw [ht', ht]; linarith
    exact_mod_cast h
  have B2 : r * (z.1 - (n - d) - e) - e * (z.2 - (n + d) - r) < e + 1 := by
    have h : ((r * (z.1 - (n - d) - e) - e * (z.2 - (n + d) - r) : ℤ) : ℚ) < ((e + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht', ht]; linarith
    exact_mod_cast h
  have B3 : L - 1 < (e + r) * (z.1 - (n - d) - e) + (e - r) * (z.2 - (n + d) - r) := by
    have h : ((L - 1 : ℤ) : ℚ) < (((e + r) * (z.1 - (n - d) - e) + (e - r) * (z.2 - (n + d) - r) : ℤ) : ℚ) := by
      push_cast; rw [hs', hs]; linarith
    exact_mod_cast h
  have B4 : (e + r) * (z.1 - (n - d) - e) + (e - r) * (z.2 - (n + d) - r) <
      1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - L + 1 := by
    have h : (((e + r) * (z.1 - (n - d) - e) + (e - r) * (z.2 - (n + d) - r) : ℤ) : ℚ) <
        ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - L + 1 : ℤ) : ℚ) := by
      push_cast; rw [hs', hs]; linarith
    exact_mod_cast h
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Even sites, first copy: the window of `Q` at `z − V_P` with `a = A = min(2r, e − r)` and `l = 0`. -/
theorem inH_QB1_even (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu0 : 0 ≤ u) (hu1 : u ≤ β / 2) (hv0 : α ≤ v) (hv1 : v ≤ 1)
    (hpar : (z.1 + z.2) % 2 = 0) :
    InH ⟨r, e⟩ (z.1 - (n - d), z.2 - (n + d)) := by
  obtain ⟨hαpos, hαlt, hβpos, hβlt, hκpos, hκlt, hW, h1, hK⟩ :=
    box_facts d n e r hn hnd hr hre hdet α β κ hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := QB_real1 (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW h1 hK hu0 hu1 hv0 hv1
  have ht := t_formula_QB d n e r hdet z u v hz1 hz2
  have hs := s_formula_QB d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R1 R2 R3 R4 ht hs
  have hrq : (1 : ℚ) ≤ r := by exact_mod_cast hr
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = min (2 * r) (e - r) := ⟨_, rfl⟩
  have hAle : 2 * A ≤ e + r := by omega
  have hAq : 2 * (A : ℚ) ≤ (e : ℚ) + r := by exact_mod_cast hAle
  have hev : decide ((z.1 - (n - d) + (z.2 - (n + d))) % 2 = 0) = true := by
    rw [decide_eq_true_iff]; omega
  have hmu : muOf ⟨r, e⟩ = 1 := by
    show (if (r + e) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  rw [inH_Q_iff r e _ true hev hmu]
  have hA' : aOf ⟨r, e⟩ true = A := by rw [hA]; rfl
  have hl : lOf ⟨r, e⟩ true = 0 := rfl
  rw [hA', hl]
  dsimp only
  have C1 : A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * (z.1 - (n - d)) - e * (z.2 - (n + d)) := by
    have h : ((A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) < ((r * (z.1 - (n - d)) - e * (z.2 - (n + d)) : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith
    exact_mod_cast h
  have C2 : r * (z.1 - (n - d)) - e * (z.2 - (n + d)) < e + r - A + 1 := by
    have h : ((r * (z.1 - (n - d)) - e * (z.2 - (n + d)) : ℤ) : ℚ) < ((e + r - A + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith
    exact_mod_cast h
  have C3 : -1 < (e + r) * (z.1 - (n - d)) + (e - r) * (z.2 - (n + d)) := by
    have h : ((-1 : ℤ) : ℚ) < (((e + r) * (z.1 - (n - d)) + (e - r) * (z.2 - (n + d)) : ℤ) : ℚ) := by
      push_cast; rw [hs]; linarith
    exact_mod_cast h
  have C4 : (e + r) * (z.1 - (n - d)) + (e - r) * (z.2 - (n + d)) < 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r + 1 := by
    have h : (((e + r) * (z.1 - (n - d)) + (e - r) * (z.2 - (n + d)) : ℤ) : ℚ) <
        ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r + 1 : ℤ) : ℚ) := by
      push_cast; rw [hs]; linarith
    exact_mod_cast h
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- Even sites, second copy `Q@V_P + Q`: the lower `t` bound `hlow` is supplied (`A − T − 1 < t`). -/
theorem inH_QB2_even (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu0 : β / 2 ≤ u) (hu1 : u ≤ β) (hv0 : α ≤ v) (hv1 : v ≤ 1)
    (hpar : (z.1 + z.2) % 2 = 0)
    (A : ℤ) (hA : A = min (2 * r) (e - r))
    (hlow : A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * (z.1 - (n - d) - e) - e * (z.2 - (n + d) - r)) :
    InH ⟨r, e⟩ (z.1 - (n - d) - e, z.2 - (n + d) - r) := by
  obtain ⟨hαpos, hαlt, hβpos, hβlt, hκpos, hκlt, hW, h1, hK⟩ :=
    box_facts d n e r hn hnd hr hre hdet α β κ hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := QB_real2 (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW h1 hK hu0 hu1 hv0 hv1
  have ht := t_formula_QB d n e r hdet z u v hz1 hz2
  have hs := s_formula_QB d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R1 R2 R3 R4 ht hs
  have ht' : (r : ℚ) * ((z.1 : ℚ) - (n - d) - e) - (e : ℚ) * ((z.2 : ℚ) - (n + d) - r) =
      (r : ℚ) * ((z.1 : ℚ) - (n - d)) - (e : ℚ) * ((z.2 : ℚ) - (n + d)) := by ring
  have hs' : ((e : ℚ) + r) * ((z.1 : ℚ) - (n - d) - e) + ((e : ℚ) - r) * ((z.2 : ℚ) - (n + d) - r) =
      ((e : ℚ) + r) * ((z.1 : ℚ) - (n - d)) + ((e : ℚ) - r) * ((z.2 : ℚ) - (n + d)) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) := by
    ring
  have hrq : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hAle : 2 * A ≤ e + r := by omega
  have hAq : 2 * (A : ℚ) ≤ (e : ℚ) + r := by exact_mod_cast hAle
  have hev : decide ((z.1 - (n - d) - e + (z.2 - (n + d) - r)) % 2 = 0) = true := by
    rw [decide_eq_true_iff]; omega
  have hmu : muOf ⟨r, e⟩ = 1 := by
    show (if (r + e) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  rw [inH_Q_iff r e _ true hev hmu]
  have hA' : aOf ⟨r, e⟩ true = A := by rw [hA]; rfl
  have hl : lOf ⟨r, e⟩ true = 0 := rfl
  rw [hA', hl]
  dsimp only
  have D2 : r * (z.1 - (n - d) - e) - e * (z.2 - (n + d) - r) < e + r - A + 1 := by
    have h : ((r * (z.1 - (n - d) - e) - e * (z.2 - (n + d) - r) : ℤ) : ℚ) < ((e + r - A + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht', ht]; linarith
    exact_mod_cast h
  have D3 : -1 < (e + r) * (z.1 - (n - d) - e) + (e - r) * (z.2 - (n + d) - r) := by
    have h : ((-1 : ℤ) : ℚ) < (((e + r) * (z.1 - (n - d) - e) + (e - r) * (z.2 - (n + d) - r) : ℤ) : ℚ) := by
      push_cast; rw [hs', hs]; linarith
    exact_mod_cast h
  have D4 : (e + r) * (z.1 - (n - d) - e) + (e - r) * (z.2 - (n + d) - r) <
      1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r + 1 := by
    have h : (((e + r) * (z.1 - (n - d) - e) + (e - r) * (z.2 - (n + d) - r) : ℤ) : ℚ) <
        ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r + 1 : ℤ) : ℚ) := by
      push_cast; rw [hs', hs]; linarith
    exact_mod_cast h
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The lower `t` bound of the second copy at even sites: `A − T − 1 < t`, from `e < d` when `e = 3r`. -/
theorem QB2_low_gen (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0) (hexc : e = 3 * r → e < d)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu0 : β / 2 ≤ u) (hu1 : u ≤ β) (hv0 : α ≤ v) (hv1 : v ≤ 1)
    (A : ℤ) (hA : A = min (2 * r) (e - r)) :
    A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * (z.1 - (n - d) - e) - e * (z.2 - (n + d) - r) := by
  obtain ⟨hαpos, hαlt, hβpos, hβlt, hκpos, hκlt, hW, h1, hK⟩ :=
    box_facts d n e r hn hnd hr hre hdet α β κ hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := QB_real2 (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW h1 hK hu0 hu1 hv0 hv1
  have ht := t_formula_QB d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R2 ht
  have ht' : (r : ℚ) * ((z.1 : ℚ) - (n - d) - e) - (e : ℚ) * ((z.2 : ℚ) - (n + d) - r) =
      (r : ℚ) * ((z.1 : ℚ) - (n - d)) - (e : ℚ) * ((z.2 : ℚ) - (n + d)) := by ring
  have hAq : 2 * (A : ℚ) ≤ (e : ℚ) + r := by
    have : 2 * A ≤ e + r := by omega
    exact_mod_cast this
  have hbeta : (A : ℚ) < ((e : ℚ) + r) / 2 + 1 - 2 * β := by
    by_cases h3 : e = 3 * r
    · have hA2 : A = 2 * r := by omega
      have hedq : (e : ℚ) < d := by exact_mod_cast hexc h3
      have hDq : (0 : ℚ) < (d : ℚ) + e := by
        have : (0 : ℤ) < d + e := by omega
        exact_mod_cast this
      have hβ2 : 2 * β < 1 := by nlinarith
      have hE : (e : ℚ) = 3 * r := by exact_mod_cast h3
      rw [hA2]; push_cast; rw [hE]; linarith
    · have hA3 : 2 * A ≤ e + r - 2 := by omega
      have hA3q : 2 * (A : ℚ) ≤ (e : ℚ) + r - 2 := by exact_mod_cast hA3
      linarith
  have final : ((A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) <
      ((r * (z.1 - (n - d) - e) - e * (z.2 - (n + d) - r) : ℤ) : ℚ) := by
    push_cast; rw [ht', ht]; linarith
  exact_mod_cast final

/-- The exceptional lower `t` bound at `(d, n, e, r) = (2, 1, 3, 1)`: integrality gives `82 v ≤ 81`. -/
theorem QB2_low_exc (d n e r : ℤ) (hd : d = 2) (hn : n = 1) (he : e = 3) (hr : r = 1)
    (z : ℤ × ℤ) (_α β _κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hβ : β * ((d : ℚ) + e) = e) (hu1 : u ≤ β) (hv1 : v < 1)
    (A : ℤ) (hA : A = min (2 * r) (e - r)) :
    A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * (z.1 - (n - d) - e) - e * (z.2 - (n + d) - r) := by
  subst hd hn he hr
  have hA2 : A = 2 := by omega
  have hT : (3 : ℤ) ^ 2 + 2 * 3 * 1 - 1 ^ 2 = 14 := by norm_num
  have hβ' : β = 3 / 5 := by push_cast at hβ; linarith
  push_cast at hz1 hz2 hu1
  have hN : (82 : ℚ) * v = ((10 * z.2 - 4 * z.1 + 7 : ℤ) : ℚ) := by
    push_cast
    linear_combination (-10) * hz2 + 4 * hz1
  have hNle : 10 * z.2 - 4 * z.1 + 7 ≤ 81 := by
    have hlt : ((10 * z.2 - 4 * z.1 + 7 : ℤ) : ℚ) < 82 := by rw [← hN]; linarith
    have : 10 * z.2 - 4 * z.1 + 7 < 82 := by exact_mod_cast hlt
    omega
  have hNleq : ((10 * z.2 - 4 * z.1 + 7 : ℤ) : ℚ) ≤ 81 := by exact_mod_cast hNle
  have hreal : ((z.1 - 3 * z.2 + 10 : ℤ) : ℚ) = 12 - 2 * u - 24 * v := by
    push_cast
    linear_combination hz1 - 3 * hz2
  have hfact : (-13 : ℤ) < z.1 - 3 * z.2 + 10 := by
    have : ((-13 : ℤ) : ℚ) < ((z.1 - 3 * z.2 + 10 : ℤ) : ℚ) := by
      rw [hreal]; push_cast; linarith
    exact_mod_cast this
  rw [hA2, hT]
  omega

/-- The second copy of `Q@V_P + Q`, split at `u = β/2` (the upper half of the nominal box). -/
theorem QB_second (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu0 : β / 2 ≤ u) (hu1 : u ≤ β) (hv0 : α ≤ v) (hv1 : v < 1) :
    InH ⟨r, e⟩ (z.1 - (n - d) - e, z.2 - (n + d) - r) := by
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = min (2 * r) (e - r) := ⟨_, rfl⟩
  rcases Int.emod_two_eq_zero_or_one (z.1 + z.2) with hpar | hpar
  · by_cases hexc : e = 3 * r → e < d
    · exact inH_QB2_even d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ hu0 hu1 hv0 hv1.le hpar A hA
        (QB2_low_gen d n e r hn hnd hr hre hdet heven hexc z α β κ u v hz1 hz2 hα hβ hκ hu0 hu1 hv0 hv1.le A hA)
    · obtain ⟨hd2, hn1, he3, hr1⟩ := exc_values d n e r hn hr hdet hexc
      exact inH_QB2_even d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ hu0 hu1 hv0 hv1.le hpar A hA
        (QB2_low_exc d n e r hd2 hn1 he3 hr1 z α β κ u v hz1 hz2 hβ hu1 hv1 A hA)
  · exact inH_QB2_odd d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ hu0 hu1 hv0 hv1.le hpar

/-- The first copy `Q@V_P`, split at `u = β/2` (the lower half of the nominal box). -/
theorem QB_first (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu0 : 0 ≤ u) (hu1 : u ≤ β / 2) (hv0 : α ≤ v) (hv1 : v ≤ 1) :
    InH ⟨r, e⟩ (z.1 - (n - d), z.2 - (n + d)) := by
  rcases Int.emod_two_eq_zero_or_one (z.1 + z.2) with hpar | hpar
  · exact inH_QB1_even d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ hu0 hu1 hv0 hv1 hpar
  · exact inH_QB1_odd d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ hu0 hu1 hv0 hv1 hpar

end FLatticePaper.Tiles.PairQBBox
