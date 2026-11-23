import FLatticePaper.Tiles.SiteInduction

/-! Task 53, item 2 (covering reduction), section 7: the repeated `Q` cells of the group at `A = 2P` in the flag-true odd child.

Source (Q17, paragraph 2): "Repeated Q cells split along U." The nominal owner is the box `[α, 1] × [0, β]` of `Q`
(flag-true, `δ = dr − ne = −1`, `α = d/D`, `β = e/D`, `D = d + e`). Its local parameter `λ = (u − α)/(1 − α)` splits the two
copies: `u ≤ θ = (1 + α)/2` (that is `λ ≤ 1/2`) takes the first copy `Q@2P`, and `u ≥ θ` takes the second copy `Q@2P + Q`.

For an integer `z` of the cell with coordinates `(u, v)`, with `w = z − 2P` and `w' = z − 2P − Q`:
`t_Q(w) = t_Q(w') = 2 + (e+r)/2 − 2u − W v`, `s_Q(w) = r − 2K + 2W u + 2v`, `s_Q(w') = s_Q(w) − T`,
where `K = s_Q(P)`, `T = T_Q`, `W = K + T`, and `κ = (e − r)/D` satisfies `β K − α T = κ`. The window facets then follow from
`α, β, κ ∈ (0, 1)`, `e − r ≥ 2` and `L = min(e − r, 3r − e) ≤ r − 1`. The one real exception is the first copy's even upper `t`
bound when `e = 3r`, which needs `α > 1/2`, i.e. `d > e`. The leftover case `(d, n, e, r) = (2, 1, 3, 1)` is handled by integrality. -/

namespace FLatticePaper.Tiles.PairQAbox

open FLatticePaper.Tiles.SiteInduction

/-- `K = s_Q(P)`. -/
def Kq (d n e r : ℤ) : ℚ := ((e : ℚ) + r) * d + ((e : ℚ) - r) * n

/-- `T = T_Q = e² + 2er − r²`. -/
def Tq (e r : ℤ) : ℚ := (e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2

/-- The `t_Q` of `z − 2P` in terms of the cell coordinates `(u, v)`. -/
theorem t_formula (d n e r : ℤ) (hdet : d * r - n * e = -1) (z : ℤ × ℤ) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r))) :
    (r : ℚ) * ((z.1 : ℚ) - 2 * d) - (e : ℚ) * ((z.2 : ℚ) - 2 * n) =
      2 + ((e : ℚ) + r) / 2 - 2 * u - (Kq d n e r + Tq e r) * v := by
  have hdetQ : (d : ℚ) * r - n * e = -1 := by exact_mod_cast hdet
  unfold Kq Tq
  linear_combination (r : ℚ) * hz1 - (e : ℚ) * hz2 + (2 * u - 2) * hdetQ

/-- The `s_Q` of `z − 2P` in terms of the cell coordinates `(u, v)`. -/
theorem s_formula (d n e r : ℤ) (hdet : d * r - n * e = -1) (z : ℤ × ℤ) (u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r))) :
    ((e : ℚ) + r) * ((z.1 : ℚ) - 2 * d) + ((e : ℚ) - r) * ((z.2 : ℚ) - 2 * n) =
      r - 2 * Kq d n e r + 2 * (Kq d n e r + Tq e r) * u + 2 * v := by
  have hdetQ : (d : ℚ) * r - n * e = -1 := by exact_mod_cast hdet
  unfold Kq Tq
  linear_combination ((e : ℚ) + r) * hz1 + ((e : ℚ) - r) * hz2 - 2 * v * hdetQ

/-- The box variables `α = d/D`, `β = e/D`, `κ = (e − r)/D` and the identities they satisfy. -/
theorem ab_facts (d n e r : ℤ) (hdet : d * r - n * e = -1) (α β κ : ℚ) (hD : (d : ℚ) + e ≠ 0)
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r) :
    α + β = 1 ∧ β * Kq d n e r - α * Tq e r = κ := by
  have hdetQ : (d : ℚ) * r - n * e = -1 := by exact_mod_cast hdet
  have h1 : α + β = 1 := by
    have : (α + β) * ((d : ℚ) + e) = 1 * ((d : ℚ) + e) := by linear_combination hα + hβ
    exact mul_right_cancel₀ hD this
  refine ⟨h1, ?_⟩
  have h2 : (β * Kq d n e r - α * Tq e r) * ((d : ℚ) + e) = κ * ((d : ℚ) + e) := by
    unfold Kq Tq
    linear_combination (((e : ℚ) + r) * d + ((e : ℚ) - r) * n) * hβ
      - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) * hα - hκ - ((e : ℚ) - r) * hdetQ
  exact mul_right_cancel₀ hD h2

/-- The four real facets of the first copy on the box `[α, θ] × [0, β]`, `θ = (1 + α)/2`, in abstract variables. -/
theorem first_real (E R K T α β κ u v : ℚ) (hW : 0 ≤ K + T) (hαβ : α + β = 1) (hK : β * K - α * T = κ)
    (hu1 : α ≤ u) (hu2 : u ≤ (1 + α) / 2) (hv0 : 0 ≤ v) (hv1 : v ≤ β) :
    2 + (E + R) / 2 - 2 * u - (K + T) * v ≤ 2 + (E + R) / 2 - 2 * α ∧
    2 + (E + R) / 2 - (1 + α) - T - κ ≤ 2 + (E + R) / 2 - 2 * u - (K + T) * v ∧
    R - 2 * κ ≤ R - 2 * K + 2 * (K + T) * u + 2 * v ∧
    R - 2 * K + 2 * (K + T) * u + 2 * v ≤ T + R - κ + 2 * β := by
  have hWv : 0 ≤ (K + T) * v := mul_nonneg hW hv0
  have hWv' : (K + T) * v ≤ (K + T) * β := mul_le_mul_of_nonneg_left hv1 hW
  have hWβ : (K + T) * β = T + κ := by linear_combination hK + T * hαβ
  have hWα : (K + T) * α = K - κ := by linear_combination -hK + K * hαβ
  have hWu1 : (K + T) * α ≤ (K + T) * u := mul_le_mul_of_nonneg_left hu1 hW
  have hWu2 : (K + T) * u ≤ (K + T) * ((1 + α) / 2) := mul_le_mul_of_nonneg_left hu2 hW
  refine ⟨by linarith, by linarith, by linarith, by nlinarith⟩

/-- The four real facets of the second copy on the box `[θ, 1] × [0, β]`. The shifted `s` is `s − T`. -/
theorem second_real (E R K T α β κ u v : ℚ) (hW : 0 ≤ K + T) (hαβ : α + β = 1) (hK : β * K - α * T = κ)
    (hu1 : (1 + α) / 2 ≤ u) (hu2 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ β) :
    2 + (E + R) / 2 - 2 * u - (K + T) * v ≤ 1 + (E + R) / 2 - α ∧
    (E + R) / 2 - T - κ ≤ 2 + (E + R) / 2 - 2 * u - (K + T) * v ∧
    R - κ ≤ R - 2 * K + 2 * (K + T) * u + 2 * v - T ∧
    R - 2 * K + 2 * (K + T) * u + 2 * v - T ≤ R + T + 2 * β := by
  have hWv : 0 ≤ (K + T) * v := mul_nonneg hW hv0
  have hWv' : (K + T) * v ≤ (K + T) * β := mul_le_mul_of_nonneg_left hv1 hW
  have hWβ : (K + T) * β = T + κ := by linear_combination hK + T * hαβ
  have hWα : (K + T) * α = K - κ := by linear_combination -hK + K * hαβ
  have hWu1 : (K + T) * ((1 + α) / 2) ≤ (K + T) * u := mul_le_mul_of_nonneg_left hu1 hW
  have hWu2 : (K + T) * u ≤ (K + T) * 1 := mul_le_mul_of_nonneg_left hu2 hW
  refine ⟨by linarith, by linarith, by nlinarith, by nlinarith⟩

/-- The shared box facts: positivity of `α, β`, `0 ≤ κ < 1`, `α < 1`, `0 ≤ K + T`. -/
theorem box_facts (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (α β κ : ℚ)
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r) :
    0 < α ∧ α < 1 ∧ 0 < β ∧ β < 1 ∧ 0 ≤ κ ∧ κ < 1 ∧ 0 ≤ Kq d n e r + Tq e r ∧ α + β = 1 ∧
      β * Kq d n e r - α * Tq e r = κ := by
  have hDi : (0 : ℤ) < d + e := by omega
  have hDq : (0 : ℚ) < (d : ℚ) + e := by exact_mod_cast hDi
  have hdq : (0 : ℚ) < d := by exact_mod_cast (show (0 : ℤ) < d by omega)
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hrq : (0 : ℚ) < r := by exact_mod_cast hr
  have heq : (r : ℚ) < e := by exact_mod_cast hre
  have hndq : (n : ℚ) < d := by exact_mod_cast hnd
  have hD : (d : ℚ) + e ≠ 0 := ne_of_gt hDq
  obtain ⟨h1, hK⟩ := ab_facts d n e r hdet α β κ hD hα hβ hκ
  have hαpos : 0 < α := by
    by_contra h; push Not at h; nlinarith
  have hβpos : 0 < β := by
    by_contra h; push Not at h; nlinarith
  have hκpos : 0 ≤ κ := by
    by_contra h; push Not at h; nlinarith
  have hκlt : κ < 1 := by
    by_contra h; push Not at h; nlinarith
  have hαlt : α < 1 := by linarith
  have hβlt : β < 1 := by linarith
  have hW : 0 ≤ Kq d n e r + Tq e r := by
    unfold Kq Tq; nlinarith
  exact ⟨hαpos, hαlt, hβpos, hβlt, hκpos, hκlt, hW, h1, hK⟩

/-- `InH` of the `Q` window at a point of fixed parity `ev`. -/
theorem inH_Q_iff (r e : ℤ) (w : ℤ × ℤ) (ev : Bool) (hev : decide ((w.1 + w.2) % 2 = 0) = ev)
    (hmu : muOf ⟨r, e⟩ = 1) :
    InH ⟨r, e⟩ w ↔
      (aOf ⟨r, e⟩ ev - (e ^ 2 + 2 * e * r - r ^ 2) ≤ r * w.1 - e * w.2 ∧
        r * w.1 - e * w.2 ≤ e + r - aOf ⟨r, e⟩ ev ∧
        lOf ⟨r, e⟩ ev ≤ (e + r) * w.1 + (e - r) * w.2 ∧
        (e + r) * w.1 + (e - r) * w.2 ≤ 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - lOf ⟨r, e⟩ ev) := by
  unfold InH
  rw [hev, hmu]
  exact Iff.rfl

/-- `e ≠ 2r`, from the determinant and the parity of `e + r`. -/
theorem e_ne_two_r (d n e r : ℤ) (hr : 0 < r) (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0) :
    e ≠ 2 * r := by
  intro h
  subst h
  have h1 : r * (d - 2 * n) = -1 := by linarith
  have hneg : d - 2 * n < 0 := by
    by_contra hc
    push Not at hc
    nlinarith
  have h2 : d - 2 * n ≤ -1 := by omega
  have h3 : r * (d - 2 * n) ≤ r * (-1) := mul_le_mul_of_nonneg_left h2 hr.le
  have h4 : r = 1 := by nlinarith
  omega

/-- Odd sites, first copy `Q@2P`. Here `a = r` and `l = L = min(e − r, 3r − e)`. -/
theorem inH_first_odd (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu1 : α ≤ u) (hu2 : u ≤ (1 + α) / 2) (hv0 : 0 ≤ v) (hv1 : v ≤ β)
    (hpar : (z.1 + z.2) % 2 = 1) :
    InH ⟨r, e⟩ (z.1 - 2 * d, z.2 - 2 * n) := by
  obtain ⟨hαpos, hαlt, hβpos, hβlt, hκpos, hκlt, hW, h1, hK⟩ :=
    box_facts d n e r hn hnd hr hre hdet α β κ hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := first_real (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW h1 hK hu1 hu2 hv0 hv1
  have ht := t_formula d n e r hdet z u v hz1 hz2
  have hs := s_formula d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R1 R2 R3 R4 ht hs
  have hE2 : (2 : ℚ) ≤ (e : ℚ) - r := by
    have h : (2 : ℤ) ≤ e - r := by omega
    exact_mod_cast h
  have hne := e_ne_two_r d n e r hr hdet heven
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = min (e - r) (3 * r - e) := ⟨_, rfl⟩
  have hLle : L ≤ r - 1 := by omega
  have hLq : (L : ℚ) ≤ (r : ℚ) - 1 := by exact_mod_cast hLle
  have hev : decide ((z.1 - 2 * d + (z.2 - 2 * n)) % 2 = 0) = false := by
    rw [decide_eq_false_iff_not]; omega
  have hmu : muOf ⟨r, e⟩ = 1 := by
    show (if (r + e) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  rw [inH_Q_iff r e _ false hev hmu]
  have hA : aOf ⟨r, e⟩ false = r := rfl
  have hl : lOf ⟨r, e⟩ false = L := by rw [hL]; rfl
  rw [hA, hl]
  dsimp only
  have A1 : r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * (z.1 - 2 * d) - e * (z.2 - 2 * n) := by
    have h : ((r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) < ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith
    exact_mod_cast h
  have A2 : r * (z.1 - 2 * d) - e * (z.2 - 2 * n) < e + 1 := by
    have h : ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) < ((e + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith
    exact_mod_cast h
  have A3 : L - 1 < (e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) := by
    have h : ((L - 1 : ℤ) : ℚ) < (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) := by
      push_cast; rw [hs]; linarith
    exact_mod_cast h
  have A4 : (e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) < 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - L + 1 := by
    have h : (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) <
        ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - L + 1 : ℤ) : ℚ) := by
      push_cast; rw [hs]; linarith
    exact_mod_cast h
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The upper `t` bound of the first copy at even sites: `t ≤ e + r − min(2r, e − r)`. The case `e = 3r` needs `d > e`. -/
theorem first_top_even (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0) (hexc : e = 3 * r → e < d)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu1 : α ≤ u) (hu2 : u ≤ (1 + α) / 2) (hv0 : 0 ≤ v) (hv1 : v ≤ β) :
    r * (z.1 - 2 * d) - e * (z.2 - 2 * n) ≤ e + r - min (2 * r) (e - r) := by
  obtain ⟨hαpos, hαlt, hβpos, hβlt, hκpos, hκlt, hW, h1, hK⟩ :=
    box_facts d n e r hn hnd hr hre hdet α β κ hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := first_real (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW h1 hK hu1 hu2 hv0 hv1
  have ht := t_formula d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R1 ht
  have hE2 : (2 : ℚ) ≤ (e : ℚ) - r := by
    have h : (2 : ℤ) ≤ e - r := by omega
    exact_mod_cast h
  rcases (show e ≥ 3 * r + 2 ∨ e ≤ 3 * r - 2 ∨ e = 3 * r by omega) with h | h | h
  · have hm : min (2 * r) (e - r) = 2 * r := by omega
    rw [hm]
    have h' : ((3 * r + 2 : ℤ) : ℚ) ≤ (e : ℚ) := by exact_mod_cast h
    have key : ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) < ((e + r - 2 * r + 1 : ℤ) : ℚ) := by
      push_cast at h' ⊢; rw [ht]; linarith
    have : r * (z.1 - 2 * d) - e * (z.2 - 2 * n) < e + r - 2 * r + 1 := by exact_mod_cast key
    omega
  · have hm : min (2 * r) (e - r) = e - r := by omega
    rw [hm]
    have h' : (e : ℚ) ≤ ((3 * r - 2 : ℤ) : ℚ) := by exact_mod_cast h
    have key : ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) < ((e + r - (e - r) + 1 : ℤ) : ℚ) := by
      push_cast at h' ⊢; rw [ht]; linarith
    have : r * (z.1 - 2 * d) - e * (z.2 - 2 * n) < e + r - (e - r) + 1 := by exact_mod_cast key
    omega
  · have hm : min (2 * r) (e - r) = 2 * r := by omega
    rw [hm]
    have hed : e < d := hexc h
    have hedq : (e : ℚ) < d := by exact_mod_cast hed
    have hDq : (0 : ℚ) ≤ (d : ℚ) + e := by
      have : (0 : ℤ) < d + e := by omega
      exact_mod_cast this.le
    have hαh : 1 < 2 * α := by
      by_contra hc; push Not at hc
      nlinarith [mul_nonneg (show (0 : ℚ) ≤ 1 - 2 * α by linarith) hDq]
    have hE3 : (e : ℚ) = 3 * r := by exact_mod_cast h
    have key : ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) < ((e + r - 2 * r + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith
    have : r * (z.1 - 2 * d) - e * (z.2 - 2 * n) < e + r - 2 * r + 1 := by exact_mod_cast key
    omega

/-- The four integer facts of the first copy at even sites, given the upper `t` bound `htop`. -/
theorem inH_first_even (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu1 : α ≤ u) (hu2 : u ≤ (1 + α) / 2) (hv0 : 0 ≤ v) (hv1 : v ≤ β)
    (hpar : (z.1 + z.2) % 2 = 0)
    (htop : r * (z.1 - 2 * d) - e * (z.2 - 2 * n) ≤ e + r - min (2 * r) (e - r)) :
    InH ⟨r, e⟩ (z.1 - 2 * d, z.2 - 2 * n) := by
  obtain ⟨hαpos, hαlt, hβpos, hβlt, hκpos, hκlt, hW, h1, hK⟩ :=
    box_facts d n e r hn hnd hr hre hdet α β κ hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := first_real (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW h1 hK hu1 hu2 hv0 hv1
  have ht := t_formula d n e r hdet z u v hz1 hz2
  have hs := s_formula d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R1 R2 R3 R4 ht hs
  have hrq : (1 : ℚ) ≤ r := by exact_mod_cast hr
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = min (2 * r) (e - r) := ⟨_, rfl⟩
  have hAle : 2 * A ≤ e + r := by omega
  have hAq : 2 * (A : ℚ) ≤ (e : ℚ) + r := by exact_mod_cast hAle
  have hev : decide ((z.1 - 2 * d + (z.2 - 2 * n)) % 2 = 0) = true := by
    rw [decide_eq_true_iff]; omega
  have hmu : muOf ⟨r, e⟩ = 1 := by
    show (if (r + e) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  rw [inH_Q_iff r e _ true hev hmu]
  have hA' : aOf ⟨r, e⟩ true = A := by rw [hA]; rfl
  have hl : lOf ⟨r, e⟩ true = 0 := rfl
  rw [hA', hl]
  dsimp only
  rw [← hA] at htop
  have A1 : A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * (z.1 - 2 * d) - e * (z.2 - 2 * n) := by
    have h : ((A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) < ((r * (z.1 - 2 * d) - e * (z.2 - 2 * n) : ℤ) : ℚ) := by
      push_cast; rw [ht]; linarith
    exact_mod_cast h
  have A3 : -1 < (e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) := by
    have h : ((-1 : ℤ) : ℚ) < (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) := by
      push_cast; rw [hs]; linarith
    exact_mod_cast h
  have A4 : (e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) < 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r + 1 := by
    have h : (((e + r) * (z.1 - 2 * d) + (e - r) * (z.2 - 2 * n) : ℤ) : ℚ) <
        ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r + 1 : ℤ) : ℚ) := by
      push_cast; rw [hs]; linarith
    exact_mod_cast h
  refine ⟨by linarith, htop, by linarith, by linarith⟩

/-- The four integer facts of the second copy at odd sites: the window of `Q` at `z − 2P − Q` (with `a = r`, `l = L`). -/
theorem inH_second_odd (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu1 : (1 + α) / 2 ≤ u) (hu2 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ β)
    (hpar : (z.1 + z.2) % 2 = 1) :
    InH ⟨r, e⟩ (z.1 - 2 * d - e, z.2 - 2 * n - r) := by
  obtain ⟨hαpos, hαlt, hβpos, hβlt, hκpos, hκlt, hW, h1, hK⟩ :=
    box_facts d n e r hn hnd hr hre hdet α β κ hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := second_real (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW h1 hK hu1 hu2 hv0 hv1
  have ht := t_formula d n e r hdet z u v hz1 hz2
  have hs := s_formula d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R1 R2 R3 R4 ht hs
  have ht' : (r : ℚ) * ((z.1 : ℚ) - 2 * d - e) - (e : ℚ) * ((z.2 : ℚ) - 2 * n - r) =
      (r : ℚ) * ((z.1 : ℚ) - 2 * d) - (e : ℚ) * ((z.2 : ℚ) - 2 * n) := by ring
  have hs' : ((e : ℚ) + r) * ((z.1 : ℚ) - 2 * d - e) + ((e : ℚ) - r) * ((z.2 : ℚ) - 2 * n - r) =
      ((e : ℚ) + r) * ((z.1 : ℚ) - 2 * d) + ((e : ℚ) - r) * ((z.2 : ℚ) - 2 * n) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) := by
    ring
  have hE2 : (2 : ℚ) ≤ (e : ℚ) - r := by
    have h : (2 : ℤ) ≤ e - r := by omega
    exact_mod_cast h
  obtain ⟨L, hL⟩ : ∃ L : ℤ, L = min (e - r) (3 * r - e) := ⟨_, rfl⟩
  have hLle : L ≤ r - 1 := by
    have hne := e_ne_two_r d n e r hr hdet heven
    omega
  have hLq : (L : ℚ) ≤ (r : ℚ) - 1 := by exact_mod_cast hLle
  have hev : decide ((z.1 - 2 * d - e + (z.2 - 2 * n - r)) % 2 = 0) = false := by
    rw [decide_eq_false_iff_not]; omega
  have hmu : muOf ⟨r, e⟩ = 1 := by
    show (if (r + e) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  rw [inH_Q_iff r e _ false hev hmu]
  have hA : aOf ⟨r, e⟩ false = r := rfl
  have hl : lOf ⟨r, e⟩ false = L := by rw [hL]; rfl
  rw [hA, hl]
  dsimp only
  have B1 : r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * (z.1 - 2 * d - e) - e * (z.2 - 2 * n - r) := by
    have h : ((r - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) < ((r * (z.1 - 2 * d - e) - e * (z.2 - 2 * n - r) : ℤ) : ℚ) := by
      push_cast; rw [ht', ht]; linarith
    exact_mod_cast h
  have B2 : r * (z.1 - 2 * d - e) - e * (z.2 - 2 * n - r) < e + 1 := by
    have h : ((r * (z.1 - 2 * d - e) - e * (z.2 - 2 * n - r) : ℤ) : ℚ) < ((e + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht', ht]; linarith
    exact_mod_cast h
  have B3 : L - 1 < (e + r) * (z.1 - 2 * d - e) + (e - r) * (z.2 - 2 * n - r) := by
    have h : ((L - 1 : ℤ) : ℚ) < (((e + r) * (z.1 - 2 * d - e) + (e - r) * (z.2 - 2 * n - r) : ℤ) : ℚ) := by
      push_cast; rw [hs', hs]; linarith
    exact_mod_cast h
  have B4 : (e + r) * (z.1 - 2 * d - e) + (e - r) * (z.2 - 2 * n - r) <
      1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - L + 1 := by
    have h : (((e + r) * (z.1 - 2 * d - e) + (e - r) * (z.2 - 2 * n - r) : ℤ) : ℚ) <
        ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r - L + 1 : ℤ) : ℚ) := by
      push_cast; rw [hs', hs]; linarith
    exact_mod_cast h
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The four integer facts of the second copy at even sites. -/
theorem inH_second_even (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu1 : (1 + α) / 2 ≤ u) (hu2 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ β)
    (hpar : (z.1 + z.2) % 2 = 0) :
    InH ⟨r, e⟩ (z.1 - 2 * d - e, z.2 - 2 * n - r) := by
  obtain ⟨hαpos, hαlt, hβpos, hβlt, hκpos, hκlt, hW, h1, hK⟩ :=
    box_facts d n e r hn hnd hr hre hdet α β κ hα hβ hκ
  obtain ⟨R1, R2, R3, R4⟩ := second_real (e : ℚ) (r : ℚ) (Kq d n e r) (Tq e r) α β κ u v hW h1 hK hu1 hu2 hv0 hv1
  have ht := t_formula d n e r hdet z u v hz1 hz2
  have hs := s_formula d n e r hdet z u v hz1 hz2
  unfold Kq Tq at R1 R2 R3 R4 ht hs
  have ht' : (r : ℚ) * ((z.1 : ℚ) - 2 * d - e) - (e : ℚ) * ((z.2 : ℚ) - 2 * n - r) =
      (r : ℚ) * ((z.1 : ℚ) - 2 * d) - (e : ℚ) * ((z.2 : ℚ) - 2 * n) := by ring
  have hs' : ((e : ℚ) + r) * ((z.1 : ℚ) - 2 * d - e) + ((e : ℚ) - r) * ((z.2 : ℚ) - 2 * n - r) =
      ((e : ℚ) + r) * ((z.1 : ℚ) - 2 * d) + ((e : ℚ) - r) * ((z.2 : ℚ) - 2 * n) - ((e : ℚ) ^ 2 + 2 * e * r - (r : ℚ) ^ 2) := by
    ring
  have hE2 : (2 : ℚ) ≤ (e : ℚ) - r := by
    have h : (2 : ℤ) ≤ e - r := by omega
    exact_mod_cast h
  have hrq : (1 : ℚ) ≤ r := by exact_mod_cast hr
  obtain ⟨A, hA⟩ : ∃ A : ℤ, A = min (2 * r) (e - r) := ⟨_, rfl⟩
  have hAle : 2 * A ≤ e + r := by omega
  have hAq : 2 * (A : ℚ) ≤ (e : ℚ) + r := by exact_mod_cast hAle
  have hev : decide ((z.1 - 2 * d - e + (z.2 - 2 * n - r)) % 2 = 0) = true := by
    rw [decide_eq_true_iff]; omega
  have hmu : muOf ⟨r, e⟩ = 1 := by
    show (if (r + e) % 2 = 1 then 2 else 1) = 1
    rw [if_neg (by omega)]
  rw [inH_Q_iff r e _ true hev hmu]
  have hA' : aOf ⟨r, e⟩ true = A := by rw [hA]; rfl
  have hl : lOf ⟨r, e⟩ true = 0 := rfl
  rw [hA', hl]
  dsimp only
  have C1 : A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 < r * (z.1 - 2 * d - e) - e * (z.2 - 2 * n - r) := by
    have h : ((A - (e ^ 2 + 2 * e * r - r ^ 2) - 1 : ℤ) : ℚ) < ((r * (z.1 - 2 * d - e) - e * (z.2 - 2 * n - r) : ℤ) : ℚ) := by
      push_cast; rw [ht', ht]; linarith
    exact_mod_cast h
  have C2 : r * (z.1 - 2 * d - e) - e * (z.2 - 2 * n - r) < e + r - A + 1 := by
    have h : ((r * (z.1 - 2 * d - e) - e * (z.2 - 2 * n - r) : ℤ) : ℚ) < ((e + r - A + 1 : ℤ) : ℚ) := by
      push_cast; rw [ht', ht]; linarith
    exact_mod_cast h
  have C3 : -1 < (e + r) * (z.1 - 2 * d - e) + (e - r) * (z.2 - 2 * n - r) := by
    have h : ((-1 : ℤ) : ℚ) < (((e + r) * (z.1 - 2 * d - e) + (e - r) * (z.2 - 2 * n - r) : ℤ) : ℚ) := by
      push_cast; rw [hs', hs]; linarith
    exact_mod_cast h
  have C4 : (e + r) * (z.1 - 2 * d - e) + (e - r) * (z.2 - 2 * n - r) < 1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r + 1 := by
    have h : (((e + r) * (z.1 - 2 * d - e) + (e - r) * (z.2 - 2 * n - r) : ℤ) : ℚ) <
        ((1 * (e ^ 2 + 2 * e * r - r ^ 2) + 2 * r + 1 : ℤ) : ℚ) := by
      push_cast; rw [hs', hs]; linarith
    exact_mod_cast h
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The exceptional values: `e = 3r` with `d ≤ e` forces `(d, n, e, r) = (2, 1, 3, 1)`. -/
theorem exc_values (d n e r : ℤ) (hn : 0 < n) (hr : 0 < r) (hdet : d * r - n * e = -1)
    (hexc : ¬ (e = 3 * r → e < d)) : d = 2 ∧ n = 1 ∧ e = 3 ∧ r = 1 := by
  push Not at hexc
  obtain ⟨h3, hde⟩ := hexc
  subst h3
  have h1 : r * (d - 3 * n) = -1 := by linarith
  have hneg : d - 3 * n < 0 := by
    by_contra hc; push Not at hc; nlinarith
  have h2 : d - 3 * n ≤ -1 := by omega
  have h3' : r * (d - 3 * n) ≤ r * (-1) := mul_le_mul_of_nonneg_left h2 hr.le
  have hr1 : r = 1 := by nlinarith
  subst hr1
  omega

/-- The upper `t` bound of the first copy in the exceptional case `(d, n, e, r) = (2, 1, 3, 1)`, from integrality:
`82 v = 10 z₂ − 4 z₁ + 7` is odd, so `82 v ≥ 1`. -/
theorem first_top_exc (d n e r : ℤ) (hd : d = 2) (hn : n = 1) (he : e = 3) (hr : r = 1)
    (z : ℤ × ℤ) (α u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hu1 : α ≤ u) (hv0 : 0 ≤ v) :
    r * (z.1 - 2 * d) - e * (z.2 - 2 * n) ≤ e + r - min (2 * r) (e - r) := by
  subst hd hn he hr
  push_cast at hz1 hz2 hα
  have hα' : α = 2 / 5 := by linarith
  rw [hα'] at hu1
  have hN : (82 : ℚ) * v = ((10 * z.2 - 4 * z.1 + 7 : ℤ) : ℚ) := by
    push_cast
    linear_combination (-10) * hz2 + 4 * hz1
  have hNodd : (10 * z.2 - 4 * z.1 + 7) % 2 = 1 := by omega
  have hNnn : (0 : ℤ) ≤ 10 * z.2 - 4 * z.1 + 7 := by
    have : (0 : ℚ) ≤ ((10 * z.2 - 4 * z.1 + 7 : ℤ) : ℚ) := by
      rw [← hN]; linarith
    exact_mod_cast this
  have hN1 : (1 : ℤ) ≤ 10 * z.2 - 4 * z.1 + 7 := by omega
  have hN1q : (1 : ℚ) ≤ ((10 * z.2 - 4 * z.1 + 7 : ℤ) : ℚ) := by exact_mod_cast hN1
  have hv82 : (1 : ℚ) ≤ 82 * v := by linarith
  have key : (z.1 : ℚ) - 3 * z.2 + 2 < 3 := by linarith
  have hint : z.1 - 3 * z.2 + 2 < 3 := by exact_mod_cast key
  omega

/-- **The first copy `Q@2P` owns the points of the box with `u ≤ θ`** (the lower half of the nominal Q box, `λ ≤ 1/2`). -/
theorem QA_first (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu1 : α ≤ u) (hu2 : u ≤ (1 + α) / 2) (hv0 : 0 ≤ v) (hv1 : v ≤ β) :
    InH ⟨r, e⟩ (z.1 - 2 * d, z.2 - 2 * n) := by
  rcases Int.emod_two_eq_zero_or_one (z.1 + z.2) with hpar | hpar
  · by_cases hexc : e = 3 * r → e < d
    · exact inH_first_even d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ hu1 hu2 hv0 hv1 hpar
        (first_top_even d n e r hn hnd hr hre hdet heven hexc z α β κ u v hz1 hz2 hα hβ hκ hu1 hu2 hv0 hv1)
    · obtain ⟨hd2, hn1, he3, hr1⟩ := exc_values d n e r hn hr hdet hexc
      exact inH_first_even d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ hu1 hu2 hv0 hv1 hpar
        (first_top_exc d n e r hd2 hn1 he3 hr1 z α u v hz1 hz2 hα hu1 hv0)
  · exact inH_first_odd d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ hu1 hu2 hv0 hv1 hpar

/-- **The second copy `Q@2P + Q` owns the points of the box with `u ≥ θ`** (the upper half of the nominal Q box, `λ ≥ 1/2`). -/
theorem QA_second (d n e r : ℤ) (hn : 0 < n) (hnd : n < d) (hr : 0 < r) (hre : r < e)
    (hdet : d * r - n * e = -1) (heven : (e + r) % 2 = 0)
    (z : ℤ × ℤ) (α β κ u v : ℚ)
    (hz1 : (z.1 : ℚ) - 1 / 2 = u * (2 * ((d : ℚ) + e)) + v * ((n : ℚ) + r - ((d : ℚ) + e)))
    (hz2 : (z.2 : ℚ) + 1 / 2 = u * (2 * ((n : ℚ) + r)) + v * ((d : ℚ) + e + ((n : ℚ) + r)))
    (hα : α * ((d : ℚ) + e) = d) (hβ : β * ((d : ℚ) + e) = e) (hκ : κ * ((d : ℚ) + e) = (e : ℚ) - r)
    (hu1 : (1 + α) / 2 ≤ u) (hu2 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ β) :
    InH ⟨r, e⟩ (z.1 - 2 * d - e, z.2 - 2 * n - r) := by
  rcases Int.emod_two_eq_zero_or_one (z.1 + z.2) with hpar | hpar
  · exact inH_second_even d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ hu1 hu2 hv0 hv1 hpar
  · exact inH_second_odd d n e r hn hnd hr hre hdet heven z α β κ u v hz1 hz2 hα hβ hκ hu1 hu2 hv0 hv1 hpar

end FLatticePaper.Tiles.PairQAbox

