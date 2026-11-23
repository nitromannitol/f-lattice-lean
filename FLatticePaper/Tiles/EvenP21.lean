import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Task 53, item 2, section 14: the family `P = (2,1)` (HAND_THEOREM section 2) of the even child `X = 2P + Q`.

For `P = (2,1)` the determinant forces `e = 2r − 1` (flag false) or `e = 2r + 1` (flag true), with `r` odd. The real corner facets of
the odd sites fail there, but no integer point fails. The two lemmas below are the integer steps.

Let `p = 2 z₁ − 1`, `q = 2 z₂ + 1`. Then `X = 2 T u` and `Y = 2 T v` are integers, `X ≡ 2 (mod 4)` (both coefficients are even
and `p`, `q` are odd), and the box `v ≤ β` forces `Y < 2T`. A failing point has `X < 6`, so `X = 2`, which the box excludes by a
polynomial inequality. -/

namespace FLatticePaper.Tiles.EvenP21

/-- **Flag false, `P = (2,1)`, the odd-site lower facet of `F1`**: `(e + r) z₁ + (e − r) z₂ ≥ e − r` for `e = 2r − 1`. -/
theorem F1_lat (r m z1 z2 : ℤ) (hr : r = 2 * m + 1) (hm : 1 ≤ m) (u v β : ℚ)
    (hz1 : (z1 : ℚ) - 1 / 2 = u * (2 * (r : ℚ) + 3) - v * ((r : ℚ) + 1))
    (hz2 : (z2 : ℚ) + 1 / 2 = u * ((r : ℚ) + 2) + v * (3 * (r : ℚ) + 5))
    (hβ : β * (2 * (r : ℚ) + 3) = 2 * (r : ℚ) - 1) (hu0 : 0 ≤ u) (hv1 : v ≤ β) :
    r - 1 ≤ (3 * r - 1) * z1 + (r - 1) * z2 := by
  have hr3 : 3 ≤ r := by omega
  have hr3q : (3 : ℚ) ≤ r := by exact_mod_cast hr3
  have hTq : (0 : ℚ) < 7 * (r : ℚ) ^ 2 + 22 * r + 17 := by nlinarith
  have hTz : (0 : ℤ) < 7 * r ^ 2 + 22 * r + 17 := by nlinarith
  obtain ⟨X, hX⟩ : ∃ X : ℤ, X = (3 * r + 5) * (2 * z1 - 1) + (r + 1) * (2 * z2 + 1) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = (2 * r + 3) * (2 * z2 + 1) - (r + 2) * (2 * z1 - 1) := ⟨_, rfl⟩
  have hXq : (X : ℚ) = 2 * (7 * (r : ℚ) ^ 2 + 22 * r + 17) * u := by
    rw [hX]; push_cast
    linear_combination (2 * (3 * (r : ℚ) + 5)) * hz1 + (2 * ((r : ℚ) + 1)) * hz2
  have hYq : (Y : ℚ) = 2 * (7 * (r : ℚ) ^ 2 + 22 * r + 17) * v := by
    rw [hY]; push_cast
    linear_combination (2 * (2 * (r : ℚ) + 3)) * hz2 - (2 * ((r : ℚ) + 2)) * hz1
  have hX0 : 0 ≤ X := by
    have : (0 : ℚ) ≤ X := by
      rw [hXq]
      exact mul_nonneg (by linarith) hu0
    exact_mod_cast this
  -- the box bound on `Y`: `(2r+3) Y ≤ 2 (2r−1) T`
  have hYb : (2 * r + 3) * Y ≤ 2 * (2 * r - 1) * (7 * r ^ 2 + 22 * r + 17) := by
    have h1 : (2 * (r : ℚ) + 3) * (2 * (7 * (r : ℚ) ^ 2 + 22 * r + 17) * v) ≤
        (2 * (r : ℚ) + 3) * (2 * (7 * (r : ℚ) ^ 2 + 22 * r + 17) * β) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_left hv1 (by linarith)
    have h2 : (2 * (r : ℚ) + 3) * (2 * (7 * (r : ℚ) ^ 2 + 22 * r + 17) * β) =
        2 * (2 * (r : ℚ) - 1) * (7 * (r : ℚ) ^ 2 + 22 * r + 17) := by
      linear_combination (2 * (7 * (r : ℚ) ^ 2 + 22 * r + 17)) * hβ
    have h3 : (2 * (r : ℚ) + 3) * (Y : ℚ) = (2 * (r : ℚ) + 3) * (2 * (7 * (r : ℚ) ^ 2 + 22 * r + 17) * v) := by
      rw [hYq]
    have h4 : (2 * (r : ℚ) + 3) * (Y : ℚ) ≤ 2 * (2 * (r : ℚ) - 1) * (7 * (r : ℚ) ^ 2 + 22 * r + 17) := by
      rw [h3]; linarith
    exact_mod_cast h4
  have hYlt : Y < 2 * (7 * r ^ 2 + 22 * r + 17) := by
    have h5 : (2 * r + 3) * Y < (2 * r + 3) * (2 * (7 * r ^ 2 + 22 * r + 17)) := by
      have h6 : (2 * r + 3) * (2 * (7 * r ^ 2 + 22 * r + 17)) - 2 * (2 * r - 1) * (7 * r ^ 2 + 22 * r + 17) =
          8 * (7 * r ^ 2 + 22 * r + 17) := by ring
      nlinarith
    exact lt_of_mul_lt_mul_left h5 (by omega)
  -- the key identity `T · M = G X − 4 Y`
  have hkey : (7 * r ^ 2 + 22 * r + 17) * ((3 * r - 1) * (2 * z1 - 1) + (r - 1) * (2 * z2 + 1)) =
      (7 * r ^ 2 + 8 * r - 5) * X - 4 * Y := by
    rw [hX, hY]; ring
  -- `M = 4J − 2`, and `X = 4K + 2`
  obtain ⟨J, hJ⟩ : ∃ J : ℤ, J = (3 * m + 1) * z1 + m * z2 - m := ⟨_, rfl⟩
  have hMJ : (3 * r - 1) * (2 * z1 - 1) + (r - 1) * (2 * z2 + 1) = 4 * J - 2 := by
    rw [hJ]; subst hr; ring
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = (3 * m + 4) * z1 + (m + 1) * z2 - m - 2 := ⟨_, rfl⟩
  have hXK : X = 4 * K + 2 := by
    rw [hK, hX]; subst hr; ring
  rw [hMJ] at hkey
  by_contra hc
  push Not at hc
  have hMlt : 4 * J - 2 < -2 := by
    have : (3 * r - 1) * (2 * z1 - 1) + (r - 1) * (2 * z2 + 1) < -2 := by
      linarith [hc]
    rw [hMJ] at this; exact this
  have hJneg : J ≤ -1 := by omega
  have hTM : (7 * r ^ 2 + 22 * r + 17) * (4 * J - 2) ≤ (7 * r ^ 2 + 22 * r + 17) * (-6) := by
    apply mul_le_mul_of_nonneg_left _ hTz.le
    omega
  have hfail : (7 * r ^ 2 + 8 * r - 5) * X - 4 * Y ≤ -6 * (7 * r ^ 2 + 22 * r + 17) := by
    rw [← hkey]; linarith [hTM]
  have hGpos : (0 : ℤ) < 7 * r ^ 2 + 8 * r - 5 := by nlinarith
  have hGT : (7 * r ^ 2 + 22 * r + 17 : ℤ) < 3 * (7 * r ^ 2 + 8 * r - 5) := by nlinarith
  have hXcase : X = 2 ∨ 6 ≤ X := by omega
  rcases hXcase with h2 | h6
  · -- `X = 2`: the box excludes `4 Y ≥ 2 G + 6 T`
    rw [h2] at hfail
    have h5 : 2 * (7 * r ^ 2 + 8 * r - 5) + 6 * (7 * r ^ 2 + 22 * r + 17) ≤ 4 * Y := by linarith [hfail]
    have h7 : (2 * r + 3) * (2 * (7 * r ^ 2 + 8 * r - 5) + 6 * (7 * r ^ 2 + 22 * r + 17)) ≤
        (2 * r + 3) * (4 * Y) := mul_le_mul_of_nonneg_left h5 (by omega)
    have h8 : (2 * r + 3) * (4 * Y) = 4 * ((2 * r + 3) * Y) := by ring
    have hpoly : 8 * (2 * r - 1) * (7 * r ^ 2 + 22 * r + 17) <
        (2 * r + 3) * (2 * (7 * r ^ 2 + 8 * r - 5) + 6 * (7 * r ^ 2 + 22 * r + 17)) := by
      have hp : (2 * r + 3) * (2 * (7 * r ^ 2 + 8 * r - 5) + 6 * (7 * r ^ 2 + 22 * r + 17)) -
          8 * (2 * r - 1) * (7 * r ^ 2 + 22 * r + 17) = 2 * (84 * r ^ 2 + 266 * r + 206) := by ring
      have hq : (0 : ℤ) < 84 * r ^ 2 + 266 * r + 206 := by nlinarith
      linarith
    linarith [hYb, h7, h8, hpoly]
  · -- `X ≥ 6`: then `4Y ≥ 6G + 6T` contradicts `Y < 2T` and `T < 3G`
    have h9 : (7 * r ^ 2 + 8 * r - 5) * 6 ≤ (7 * r ^ 2 + 8 * r - 5) * X :=
      mul_le_mul_of_nonneg_left h6 hGpos.le
    linarith [hfail, h9, hYlt, hGT]

/-- Integer core of the flag-true lattice step. With `G = 7r² + 20r + 7`, `T = 7r² + 34r + 41`, the failing relation
`G X + 4 Y ≥ 2 T G + 6 T` with `X ≡ 2 (mod 4)`, `X ≤ 2T`, `(2r+5) Y ≤ 2(2r+1) T` and `T ≡ 2 (mod 4)` is impossible. -/
theorem T1_core (r X Y K a : ℤ) (hr3 : 3 ≤ r) (hXK : X = 4 * K + 2) (hTa : 7 * r ^ 2 + 34 * r + 41 = 4 * a + 2)
    (hXle : X ≤ 2 * (7 * r ^ 2 + 34 * r + 41)) (hYlt : Y < 2 * (7 * r ^ 2 + 34 * r + 41))
    (hYb : (2 * r + 5) * Y ≤ 2 * (2 * r + 1) * (7 * r ^ 2 + 34 * r + 41))
    (hfail : (7 * r ^ 2 + 20 * r + 7) * X + 4 * Y ≥
      2 * (7 * r ^ 2 + 34 * r + 41) * (7 * r ^ 2 + 20 * r + 7) + 6 * (7 * r ^ 2 + 34 * r + 41)) : False := by
  obtain ⟨G, hG⟩ : ∃ G : ℤ, G = 7 * r ^ 2 + 20 * r + 7 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℤ, T = 7 * r ^ 2 + 34 * r + 41 := ⟨_, rfl⟩
  rw [← hG, ← hT] at hfail
  rw [← hT] at hXle hYlt hYb hTa
  have hGpos : 0 < G := by rw [hG]; nlinarith
  have h2TG : 2 * T < 4 * G := by rw [hG, hT]; nlinarith
  have hx0 : 0 ≤ 2 * T - X := by linarith
  have hx4 : 2 * T - X < 4 := by
    by_contra hc4
    push Not at hc4
    have hmul : G * 4 ≤ G * (2 * T - X) := mul_le_mul_of_nonneg_left hc4 hGpos.le
    nlinarith
  have hx2 : 2 * T - X = 2 := by omega
  have hXT : X = 2 * T - 2 := by omega
  rw [hXT] at hfail
  have h5 : 2 * G + 6 * T ≤ 4 * Y := by nlinarith
  have hr5 : (0 : ℤ) ≤ 2 * r + 5 := by omega
  have h7 : (2 * r + 5) * (2 * G + 6 * T) ≤ (2 * r + 5) * (4 * Y) := mul_le_mul_of_nonneg_left h5 hr5
  have hpoly : 2 * (2 * r + 1) * T * 4 < (2 * r + 5) * (2 * G + 6 * T) := by
    rw [hG, hT]
    have hq2 : (0 : ℤ) < 84 * r ^ 2 + 406 * r + 486 := by nlinarith
    nlinarith
  nlinarith

/-- **Flag true, `P = (2,1)`, the odd-site upper facet of `T1`**: with `e = 2r + 1`, `w = z − 2P`, `(e+r) w₁ + (e−r) w₂ ≤ T_Q + r + 1`. -/
theorem T1_lat (r m z1 z2 : ℤ) (hr : r = 2 * m + 1) (hm : 1 ≤ m) (u v β : ℚ)
    (hz1 : (z1 : ℚ) - 1 / 2 = u * (2 * (r : ℚ) + 5) - v * ((r : ℚ) + 3))
    (hz2 : (z2 : ℚ) + 1 / 2 = u * ((r : ℚ) + 2) + v * (3 * (r : ℚ) + 7))
    (hβ : β * (2 * (r : ℚ) + 5) = 2 * (r : ℚ) + 1) (hu1 : u ≤ 1) (hv1 : v ≤ β) :
    (3 * r + 1) * (z1 - 4) + (r + 1) * (z2 - 2) ≤ 7 * r ^ 2 + 7 * r + 2 := by
  have hr3 : 3 ≤ r := by omega
  have hr3q : (3 : ℚ) ≤ r := by exact_mod_cast hr3
  have hTq : (0 : ℚ) < 7 * (r : ℚ) ^ 2 + 34 * r + 41 := by nlinarith
  obtain ⟨X, hX⟩ : ∃ X : ℤ, X = (3 * r + 7) * (2 * z1 - 1) + (r + 3) * (2 * z2 + 1) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℤ, Y = (2 * r + 5) * (2 * z2 + 1) - (r + 2) * (2 * z1 - 1) := ⟨_, rfl⟩
  have hXq : (X : ℚ) = 2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41) * u := by
    rw [hX]; push_cast
    linear_combination (2 * (3 * (r : ℚ) + 7)) * hz1 + (2 * ((r : ℚ) + 3)) * hz2
  have hYq : (Y : ℚ) = 2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41) * v := by
    rw [hY]; push_cast
    linear_combination (2 * (2 * (r : ℚ) + 5)) * hz2 - (2 * ((r : ℚ) + 2)) * hz1
  have hSw : (3 * (r : ℚ) + 1) * (z1 - 4) + ((r : ℚ) + 1) * (z2 - 2) =
      (7 * (r : ℚ) ^ 2 + 20 * r + 7) * u + 4 * v - 13 * r - 6 := by
    linear_combination (3 * (r : ℚ) + 1) * hz1 + ((r : ℚ) + 1) * hz2
  obtain ⟨Wh, hWh⟩ : ∃ Wh : ℤ, Wh = (3 * m + 2) * (z1 - 4) + (m + 1) * (z2 - 2) - (14 * m ^ 2 + 21 * m + 8) :=
    ⟨_, rfl⟩
  have hWh2 : (3 * r + 1) * (z1 - 4) + (r + 1) * (z2 - 2) - (7 * r ^ 2 + 7 * r + 2) = 2 * Wh := by
    rw [hWh]; subst hr; ring
  have hrel : (7 * (r : ℚ) ^ 2 + 20 * r + 7) * (X : ℚ) + 4 * (Y : ℚ) =
      2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41) * ((7 * (r : ℚ) ^ 2 + 20 * r + 7) + 1) +
        2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41) * (2 * (Wh : ℚ)) := by
    have hW : (2 * (Wh : ℚ)) = (3 * (r : ℚ) + 1) * (z1 - 4) + ((r : ℚ) + 1) * (z2 - 2) -
        (7 * (r : ℚ) ^ 2 + 7 * r + 2) := by
      have := congrArg (fun t : ℤ => (t : ℚ)) hWh2
      push_cast at this
      linarith
    rw [hW, hXq, hYq, hSw]
    ring
  by_contra hc
  push Not at hc
  have hWpos : 1 ≤ Wh := by
    have : (7 * r ^ 2 + 7 * r + 2 : ℤ) < (3 * r + 1) * (z1 - 4) + (r + 1) * (z2 - 2) := by linarith
    omega
  obtain ⟨K, hK⟩ : ∃ K : ℤ, K = (3 * m + 5) * z1 + (m + 2) * z2 - m - 2 := ⟨_, rfl⟩
  have hXK : X = 4 * K + 2 := by
    rw [hK, hX]; subst hr; ring
  obtain ⟨a, ha⟩ : ∃ a : ℤ, a = 7 * m ^ 2 + 24 * m + 20 := ⟨_, rfl⟩
  have hTa : 7 * r ^ 2 + 34 * r + 41 = 4 * a + 2 := by
    rw [ha]; subst hr; ring
  have hYb : (2 * r + 5) * Y ≤ 2 * (2 * r + 1) * (7 * r ^ 2 + 34 * r + 41) := by
    have h1 : (2 * (r : ℚ) + 5) * (2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41) * v) ≤
        (2 * (r : ℚ) + 5) * (2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41) * β) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_left hv1 (by linarith)
    have h2 : (2 * (r : ℚ) + 5) * (2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41) * β) =
        2 * (2 * (r : ℚ) + 1) * (7 * (r : ℚ) ^ 2 + 34 * r + 41) := by
      linear_combination (2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41)) * hβ
    have h3 : (2 * (r : ℚ) + 5) * (Y : ℚ) = (2 * (r : ℚ) + 5) * (2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41) * v) := by
      rw [hYq]
    have h4 : (2 * (r : ℚ) + 5) * (Y : ℚ) ≤ 2 * (2 * (r : ℚ) + 1) * (7 * (r : ℚ) ^ 2 + 34 * r + 41) := by
      rw [h3]; linarith
    exact_mod_cast h4
  have hYlt : Y < 2 * (7 * r ^ 2 + 34 * r + 41) := by
    have h5 : (2 * r + 5) * Y < (2 * r + 5) * (2 * (7 * r ^ 2 + 34 * r + 41)) := by
      have h6 : (2 * r + 5) * (2 * (7 * r ^ 2 + 34 * r + 41)) - 2 * (2 * r + 1) * (7 * r ^ 2 + 34 * r + 41) =
          8 * (7 * r ^ 2 + 34 * r + 41) := by ring
      have h7 : (0 : ℤ) < 7 * r ^ 2 + 34 * r + 41 := by nlinarith
      linarith
    exact lt_of_mul_lt_mul_left h5 (by omega)
  have hXle : X ≤ 2 * (7 * r ^ 2 + 34 * r + 41) := by
    have h1 : (X : ℚ) ≤ 2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41) := by
      rw [hXq]
      have h2 := mul_le_mul_of_nonneg_left hu1 (by linarith : (0 : ℚ) ≤ 2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41))
      linarith
    exact_mod_cast h1
  have hfail : (7 * r ^ 2 + 20 * r + 7) * X + 4 * Y ≥
      2 * (7 * r ^ 2 + 34 * r + 41) * (7 * r ^ 2 + 20 * r + 7) + 6 * (7 * r ^ 2 + 34 * r + 41) := by
    have hWq : (1 : ℚ) ≤ (Wh : ℚ) := by exact_mod_cast hWpos
    have hT2 : (0 : ℚ) ≤ 2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41) := by linarith
    have h10 : 2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41) * 1 ≤ 2 * (7 * (r : ℚ) ^ 2 + 34 * r + 41) * (Wh : ℚ) :=
      mul_le_mul_of_nonneg_left hWq hT2
    have hq : (((7 * r ^ 2 + 20 * r + 7) * X + 4 * Y : ℤ) : ℚ) ≥
        ((2 * (7 * r ^ 2 + 34 * r + 41) * (7 * r ^ 2 + 20 * r + 7) + 6 * (7 * r ^ 2 + 34 * r + 41) : ℤ) : ℚ) := by
      push_cast
      linarith [hrel, h10]
    exact_mod_cast hq
  exact T1_core r X Y K a hr3 hXK hTa hXle hYlt hYb hfail

end FLatticePaper.Tiles.EvenP21
