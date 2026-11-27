import FLatticePaper.Plane.SurgicalH0
import FLatticePaper.Tiles.ZeroOneOdometers

/-! The vertical identities of Lemma A(b) of the standard decompositions (condition (C)), with the harmonic correction
`h_0` of eq:harmonic_h0. `zoH0 = -centeredQuarterTurnCorrection` (`FLatticePaper.surgical_h0_integer_harmonic`).

* `zoH0_shift_even`: for `v` with even coordinate sum, `h_0(x+v) - h_0(x) = ℓ(v)·x + h_0(v)` with `ℓ(v) = (p, q)`,
  `2p = -v_1 - v_2`, `2q = v_2 - v_1` (manuscript (1)).
* `zoH0_shift_mm`: the instance `h_0(x - v_{m/k,2}) - h_0(x) = a_{m/k,2}·x + h_0(-v_{m/k,2})`, `a_{m/k,2} = (m, -k)`
  (manuscript (2)).
* `zoH0_one_tile`, `zoH0_zero_plus`, `zoH0_zero_minus`: the three pointwise identities on `T_{1/1}` and `T_{0/1}` with the
  base odometers `oneOdometer`, `zeroOdometer` of `ZeroOneOdometers`, for `a_{1/1,2} = (1, -1)`. -/

namespace FLatticePaper.Tiles

open FLatticePaper.Construction

/-- The manuscript's `h_0` (eq:harmonic_h0): the negative of the centered quarter-turn correction. -/
abbrev zoH0 (x : Site) : ℤ := -centeredQuarterTurnCorrection x

theorem zoH0_four (x : Site) :
    4 * zoH0 x = -x.1 ^ 2 - 2 * x.1 * x.2 + x.2 ^ 2 + 2 * x.2 + (x.1 + x.2) % 2 :=
  (FLatticePaper.surgical_h0_integer_harmonic).2 x

/-- Manuscript (1): the translation identity for `h_0` when `v_1 + v_2` is even. -/
theorem zoH0_shift_even (x v : Site) (p q : ℤ) (hp : 2 * p = -v.1 - v.2) (hq : 2 * q = v.2 - v.1)
    (hv : (v.1 + v.2) % 2 = 0) :
    zoH0 (x + v) - zoH0 x = p * x.1 + q * x.2 + zoH0 v := by
  have h1 := zoH0_four (x + v)
  have h2 := zoH0_four x
  have h3 := zoH0_four v
  have hpar : ((x.1 + v.1) + (x.2 + v.2)) % 2 = (x.1 + x.2) % 2 := by omega
  have h1' : 4 * zoH0 (x + v) = -(x.1 + v.1) ^ 2 - 2 * (x.1 + v.1) * (x.2 + v.2) + (x.2 + v.2) ^ 2
      + 2 * (x.2 + v.2) + ((x.1 + v.1) + (x.2 + v.2)) % 2 := by
    simpa [Prod.fst_add, Prod.snd_add] using h1
  apply mul_left_cancel₀ (show (4 : ℤ) ≠ 0 by norm_num)
  linear_combination h1' - h2 - h3 - 2 * x.1 * hp - 2 * x.2 * hq + hpar - hv

/-- Manuscript (2): the instance at `-v_{m/k,2}`, `v_{m/k,2} = (m - k, m + k)` and `a_{m/k,2} = (m, -k)`. -/
theorem zoH0_shift_mm (x : Site) (m k : ℤ) :
    zoH0 (x - (m - k, m + k)) - zoH0 x = m * x.1 + (-k) * x.2 + zoH0 (-(m - k), -(m + k)) := by
  have e : x - (m - k, m + k) = x + (-(m - k), -(m + k)) := by
    ext <;> simp [sub_eq_add_neg]
  rw [e]
  exact zoH0_shift_even x (-(m - k), -(m + k)) m (-k) (by simp; ring) (by simp; ring) (by simp; omega)

/-- Manuscript: `o_{1/1}(u) + h_0(u) = 0` on `T_{1/1}`. -/
theorem zoH0_one_tile (u : Site) (hu : u ∈ oneTileSites) : oneOdometer u + zoH0 u = 0 := by
  simp only [oneTileSites, List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl <;> decide

/-- Manuscript: `o_{0/1}(u) + h_0(u - (1 + i)) = v_0^+(u) = -1{u = 0}` on `T_{0/1}`. -/
theorem zoH0_zero_plus (u : Site) (hu : u ∈ zeroTileSites) :
    zeroOdometer u + zoH0 (u.1 - 1, u.2 - 1) = if u = (0, 0) then -1 else 0 := by
  simp only [zeroTileSites, List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Manuscript: `o_{0/1}(u) + a_{1/1,2}·(u + i) + h_0(u + i) = v_0^-(u) = -1{u = 1 + 2i}` on `T_{0/1}`, with
`a_{1/1,2} = (1, -1)`. -/
theorem zoH0_zero_minus (u : Site) (hu : u ∈ zeroTileSites) :
    zeroOdometer u + (u.1 - (u.2 + 1)) + zoH0 (u.1, u.2 + 1) = if u = (1, 2) then -1 else 0 := by
  simp only [zeroTileSites, List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end FLatticePaper.Tiles
