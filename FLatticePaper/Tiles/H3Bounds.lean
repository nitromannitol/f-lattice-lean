import Mathlib.Tactic

/-! The arithmetic bounds of step 4 of the proof of (H3) in item (d) of `lemma:standard_tile_properties`.

Let `p₁ = n₁/d₁` and `q₁ = n₂/d₂` be the parents, with `n₁ d₂ - n₂ d₁ = ε = ±1`, and let the child be `n₀/d₀` with
`n₀ = c n₁ + n₂`, `d₀ = c d₁ + d₂` (`c = 1` for the odd child, `c = 2` for the even child). Write `Λ₀ = d₀ y - n₀ x` and
`S₀ = (d₀ + n₀) x + (d₀ - n₀) y`. Then `d₁ Λ₀ = d₀ Λ₁ + ε x`, `n₁ Λ₀ = n₀ Λ₁ + ε y`, `d₂ Λ₀ = d₀ Λ₂ - c ε x`,
`n₂ Λ₀ = n₀ Λ₂ - c ε y`, and the same with `S`.

* On a point `(x, y)` of the bottom walk of `T(p₁)` (`0 ≤ x ≤ 2 d₁`, `0 ≤ y ≤ 2 n₁ - 1`) with `Λ₁ ≥ -max(d₁, 2 n₁)`, `Λ₀` is at
  least `mLP` (`bound_LP`); on a point of the bottom walk of `T(q₁)` (`0 ≤ x ≤ d₂`, `0 ≤ y ≤ n₂ - 1`), at least `mLQ`
  (`bound_LQ`). These are the bounds listed in step 4 of the proof, in Case A (`2n ≤ d`, `A = true`) and Case B.
* On a point `(x, y)` of the walk of the right word of `T(p₁)` (`n₁ - d₁ + 1 ≤ x ≤ 0`, `0 ≤ y ≤ n₁ + d₁`) with the slope bound
  `S₁ ≤ d₁ + n₁ - min(0, d₁ - n₁, 3 n₁ - d₁)`, `S₀` is at most `mSP` (`bound_SP`); for `T(q₁)` at most `mSQ` (`bound_SQ`), in
  the cases `d ≤ 3n` (`A = true`) and `3n ≤ d`. These are the bounds of step 4 for the rotated quadruple, written in the
  unrotated coordinates; they replace the quarter turn of step 5. -/

namespace FLatticePaper.Tiles.H3Bounds

/-- Lower bound of `Λ₀` on the bottom walk of `T(p₁)`. -/
def mLP (A : Bool) (e n0 d0 : ℤ) : ℤ :=
  if A then (if e = -1 then -d0 - 2 else -d0 + 1) else (if e = -1 then -2 * n0 - 1 else -2 * n0)

/-- Lower bound of `Λ₀` on the bottom walk of `T(q₁)`. -/
def mLQ (A : Bool) (e c n0 d0 : ℤ) : ℤ :=
  if A then (if e = 1 then -d0 - c else -d0 + 1) else (if e = 1 then -2 * n0 - c + 1 else -2 * n0)

/-- Upper bound of `S₀` on the walk of the right word of `T(p₁)`. -/
def mSP (A : Bool) (e n0 d0 : ℤ) : ℤ :=
  if A then (if e = -1 then d0 + n0 - 1 else d0 + n0 + 2) else (if e = -1 then 2 * (d0 - n0) else 2 * (d0 - n0) + 1)

/-- Upper bound of `S₀` on the walk of the right word of `T(q₁)`. -/
def mSQ (A : Bool) (e c n0 d0 : ℤ) : ℤ :=
  if A then (if e = 1 then d0 + n0 - 1 else d0 + n0 + 2 * c)
  else (if e = 1 then 2 * (d0 - n0) else 2 * (d0 - n0) + 2 * c - 1)

theorem bound_LP (A : Bool) (n1 d1 n2 d2 c e x y : ℤ) (hc : 1 ≤ c) (hn1 : 1 ≤ n1) (hd1 : n1 < d1)
    (hn2 : 1 ≤ n2) (hd2 : n2 < d2) (hdet : n1 * d2 - n2 * d1 = e) (he : e = 1 ∨ e = -1)
    (hA : A = true → 2 * n1 ≤ d1) (hB : A = false → d1 ≤ 2 * n1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 2 * d1) (hy0 : 0 ≤ y) (hy1 : y ≤ 2 * n1 - 1)
    (hL : -max d1 (2 * n1) ≤ d1 * y - n1 * x) :
    mLP A e (c * n1 + n2) (c * d1 + d2) ≤ (c * d1 + d2) * y - (c * n1 + n2) * x := by
  have id1 : d1 * ((c * d1 + d2) * y - (c * n1 + n2) * x) = (c * d1 + d2) * (d1 * y - n1 * x) + e * x := by
    rw [← hdet]; ring
  have id2 : n1 * ((c * d1 + d2) * y - (c * n1 + n2) * x) = (c * n1 + n2) * (d1 * y - n1 * x) + e * y := by
    rw [← hdet]; ring
  have hd0 : 0 ≤ c * d1 + d2 := by nlinarith
  have hn0 : 0 ≤ c * n1 + n2 := by nlinarith
  generalize hL0 : (c * d1 + d2) * y - (c * n1 + n2) * x = L0 at id1 id2 ⊢
  generalize hL1 : d1 * y - n1 * x = L1 at id1 id2 hL
  cases A
  · have hm : max d1 (2 * n1) = 2 * n1 := max_eq_right (hB rfl)
    rw [hm] at hL
    have h1 := mul_le_mul_of_nonneg_left hL hn0
    rcases he with rfl | rfl
    · norm_num [mLP]
      have h2 : n1 * (-2 * (c * n1 + n2)) ≤ n1 * L0 := by linarith
      have := le_of_mul_le_mul_left h2 (by omega)
      linarith
    · norm_num [mLP]
      have h2 : n1 * (-2 * (c * n1 + n2) - 2) < n1 * L0 := by linarith
      have := lt_of_mul_lt_mul_left h2 (by omega)
      linarith
  · have hm : max d1 (2 * n1) = d1 := max_eq_left (hA rfl)
    rw [hm] at hL
    have h1 := mul_le_mul_of_nonneg_left hL hd0
    rcases he with rfl | rfl
    · norm_num [mLP]
      by_cases hx : x = 0
      · subst hx
        have : L0 = (c * d1 + d2) * y := by rw [← hL0]; ring
        nlinarith [mul_nonneg hd0 hy0]
      · have h2 : d1 * (-(c * d1 + d2)) < d1 * L0 := by
          have : 1 ≤ x := by omega
          linarith
        have := lt_of_mul_lt_mul_left h2 (by omega)
        linarith
    · norm_num [mLP]
      have h2 : d1 * (-(c * d1 + d2) - 2) ≤ d1 * L0 := by linarith
      have := le_of_mul_le_mul_left h2 (by omega)
      linarith

theorem bound_LQ (A : Bool) (n1 d1 n2 d2 c e x y : ℤ) (hc : 1 ≤ c) (hn1 : 1 ≤ n1) (hd1 : n1 < d1)
    (hn2 : 1 ≤ n2) (hd2 : n2 < d2) (hdet : n1 * d2 - n2 * d1 = e) (he : e = 1 ∨ e = -1)
    (hA : A = true → 2 * n2 ≤ d2) (hB : A = false → d2 ≤ 2 * n2)
    (hx0 : 0 ≤ x) (hx1 : x ≤ d2) (hy0 : 0 ≤ y) (hy1 : y ≤ n2 - 1)
    (hL : -max d2 (2 * n2) ≤ d2 * y - n2 * x) :
    mLQ A e c (c * n1 + n2) (c * d1 + d2) ≤ (c * d1 + d2) * y - (c * n1 + n2) * x := by
  have id1 : d2 * ((c * d1 + d2) * y - (c * n1 + n2) * x) = (c * d1 + d2) * (d2 * y - n2 * x) - c * e * x := by
    rw [← hdet]; ring
  have id2 : n2 * ((c * d1 + d2) * y - (c * n1 + n2) * x) = (c * n1 + n2) * (d2 * y - n2 * x) - c * e * y := by
    rw [← hdet]; ring
  have hd0 : 0 ≤ c * d1 + d2 := by nlinarith
  have hn0 : 0 ≤ c * n1 + n2 := by nlinarith
  have hc0 : 0 ≤ c := by omega
  generalize hL0 : (c * d1 + d2) * y - (c * n1 + n2) * x = L0 at id1 id2 ⊢
  generalize hL2 : d2 * y - n2 * x = L2 at id1 id2 hL
  cases A
  · have hm : max d2 (2 * n2) = 2 * n2 := max_eq_right (hB rfl)
    rw [hm] at hL
    have h1 := mul_le_mul_of_nonneg_left hL hn0
    rcases he with rfl | rfl
    · norm_num [mLQ]
      have hcy := mul_le_mul_of_nonneg_left hy1 hc0
      have h2 : n2 * (-2 * (c * n1 + n2) - c) < n2 * L0 := by nlinarith
      have := lt_of_mul_lt_mul_left h2 (by omega)
      linarith
    · norm_num [mLQ]
      have hcy := mul_nonneg hc0 hy0
      have h2 : n2 * (-2 * (c * n1 + n2)) ≤ n2 * L0 := by nlinarith
      have := le_of_mul_le_mul_left h2 (by omega)
      linarith
  · have hm : max d2 (2 * n2) = d2 := max_eq_left (hA rfl)
    rw [hm] at hL
    have h1 := mul_le_mul_of_nonneg_left hL hd0
    rcases he with rfl | rfl
    · norm_num [mLQ]
      have hcx := mul_le_mul_of_nonneg_left hx1 hc0
      have h2 : d2 * (-(c * d1 + d2) - c) ≤ d2 * L0 := by nlinarith
      have := le_of_mul_le_mul_left h2 (by omega)
      linarith
    · norm_num [mLQ]
      by_cases hx : x = 0
      · subst hx
        have : L0 = (c * d1 + d2) * y := by rw [← hL0]; ring
        nlinarith [mul_nonneg hd0 hy0]
      · have hcx := mul_le_mul_of_nonneg_left (show 1 ≤ x by omega) hc0
        have h2 : d2 * (-(c * d1 + d2)) < d2 * L0 := by nlinarith
        have := lt_of_mul_lt_mul_left h2 (by omega)
        linarith

theorem bound_SP (A : Bool) (n1 d1 n2 d2 c e x y : ℤ) (hc : 1 ≤ c) (hn1 : 1 ≤ n1) (hd1 : n1 < d1)
    (hn2 : 1 ≤ n2) (hd2 : n2 < d2) (hdet : n1 * d2 - n2 * d1 = e) (he : e = 1 ∨ e = -1)
    (hA : A = true → d1 ≤ 3 * n1) (hB : A = false → 3 * n1 ≤ d1)
    (hx0 : n1 - d1 + 1 ≤ x) (hx1 : x ≤ 0) (hy0 : 0 ≤ y) (hy1 : y ≤ n1 + d1)
    (hS : (d1 + n1) * x + (d1 - n1) * y ≤ d1 + n1 - min 0 (min (d1 - n1) (3 * n1 - d1))) :
    ((c * d1 + d2) + (c * n1 + n2)) * x + ((c * d1 + d2) - (c * n1 + n2)) * y ≤
      mSP A e (c * n1 + n2) (c * d1 + d2) := by
  have id1 : (d1 - n1) * (((c * d1 + d2) + (c * n1 + n2)) * x + ((c * d1 + d2) - (c * n1 + n2)) * y) =
      ((c * d1 + d2) - (c * n1 + n2)) * ((d1 + n1) * x + (d1 - n1) * y) - 2 * e * x := by
    rw [← hdet]; ring
  have id2 : (d1 + n1) * (((c * d1 + d2) + (c * n1 + n2)) * x + ((c * d1 + d2) - (c * n1 + n2)) * y) =
      ((c * d1 + d2) + (c * n1 + n2)) * ((d1 + n1) * x + (d1 - n1) * y) + 2 * e * y := by
    rw [← hdet]; ring
  have hdn0 : 0 ≤ (c * d1 + d2) - (c * n1 + n2) := by nlinarith
  have hsn0 : 0 ≤ (c * d1 + d2) + (c * n1 + n2) := by nlinarith
  have hs1 : 1 ≤ (c * d1 + d2) + (c * n1 + n2) := by nlinarith
  generalize hS0 : ((c * d1 + d2) + (c * n1 + n2)) * x + ((c * d1 + d2) - (c * n1 + n2)) * y = S0 at id1 id2 ⊢
  generalize hS1 : (d1 + n1) * x + (d1 - n1) * y = S1 at id1 id2 hS
  cases A
  · have hm : min 0 (min (d1 - n1) (3 * n1 - d1)) = 3 * n1 - d1 := by
      have := hB rfl
      omega
    rw [hm] at hS
    have h1 := mul_le_mul_of_nonneg_left hS hdn0
    rcases he with rfl | rfl
    · norm_num [mSP]
      have h2 : (d1 - n1) * S0 < (d1 - n1) * (2 * ((c * d1 + d2) - (c * n1 + n2)) + 2) := by nlinarith
      have := lt_of_mul_lt_mul_left h2 (by omega)
      linarith
    · norm_num [mSP]
      have h2 : (d1 - n1) * S0 ≤ (d1 - n1) * (2 * ((c * d1 + d2) - (c * n1 + n2))) := by nlinarith
      have := le_of_mul_le_mul_left h2 (by omega)
      linarith
  · have hm : min 0 (min (d1 - n1) (3 * n1 - d1)) = 0 := by
      have := hA rfl
      omega
    rw [hm] at hS
    have h1 := mul_le_mul_of_nonneg_left hS hsn0
    rcases he with rfl | rfl
    · norm_num [mSP]
      have h2 : (d1 + n1) * S0 ≤ (d1 + n1) * ((c * d1 + d2) + (c * n1 + n2) + 2) := by nlinarith
      have := le_of_mul_le_mul_left h2 (by omega)
      linarith
    · norm_num [mSP]
      by_cases hy : y = 0
      · subst hy
        have : S0 = ((c * d1 + d2) + (c * n1 + n2)) * x := by rw [← hS0]; ring
        nlinarith [mul_nonpos_iff.2 (Or.inl ⟨hsn0, hx1⟩)]
      · have h2 : (d1 + n1) * S0 < (d1 + n1) * ((c * d1 + d2) + (c * n1 + n2)) := by
          have : 1 ≤ y := by omega
          nlinarith
        have := lt_of_mul_lt_mul_left h2 (by omega)
        linarith

theorem bound_SQ (A : Bool) (n1 d1 n2 d2 c e x y : ℤ) (hc : 1 ≤ c) (hn1 : 1 ≤ n1) (hd1 : n1 < d1)
    (hn2 : 1 ≤ n2) (hd2 : n2 < d2) (hdet : n1 * d2 - n2 * d1 = e) (he : e = 1 ∨ e = -1)
    (hA : A = true → d2 ≤ 3 * n2) (hB : A = false → 3 * n2 ≤ d2)
    (hx0 : n2 - d2 + 1 ≤ x) (hx1 : x ≤ 0) (hy0 : 0 ≤ y) (hy1 : y ≤ n2 + d2)
    (hS : (d2 + n2) * x + (d2 - n2) * y ≤ d2 + n2 - min 0 (min (d2 - n2) (3 * n2 - d2))) :
    ((c * d1 + d2) + (c * n1 + n2)) * x + ((c * d1 + d2) - (c * n1 + n2)) * y ≤
      mSQ A e c (c * n1 + n2) (c * d1 + d2) := by
  have id1 : (d2 - n2) * (((c * d1 + d2) + (c * n1 + n2)) * x + ((c * d1 + d2) - (c * n1 + n2)) * y) =
      ((c * d1 + d2) - (c * n1 + n2)) * ((d2 + n2) * x + (d2 - n2) * y) + 2 * c * e * x := by
    rw [← hdet]; ring
  have id2 : (d2 + n2) * (((c * d1 + d2) + (c * n1 + n2)) * x + ((c * d1 + d2) - (c * n1 + n2)) * y) =
      ((c * d1 + d2) + (c * n1 + n2)) * ((d2 + n2) * x + (d2 - n2) * y) - 2 * c * e * y := by
    rw [← hdet]; ring
  have hdn0 : 0 ≤ (c * d1 + d2) - (c * n1 + n2) := by nlinarith
  have hsn0 : 0 ≤ (c * d1 + d2) + (c * n1 + n2) := by nlinarith
  have hs1 : 1 ≤ (c * d1 + d2) + (c * n1 + n2) := by nlinarith
  have hc0 : 0 ≤ c := by omega
  generalize hS0 : ((c * d1 + d2) + (c * n1 + n2)) * x + ((c * d1 + d2) - (c * n1 + n2)) * y = S0 at id1 id2 ⊢
  generalize hS2 : (d2 + n2) * x + (d2 - n2) * y = S2 at id1 id2 hS
  cases A
  · have hm : min 0 (min (d2 - n2) (3 * n2 - d2)) = 3 * n2 - d2 := by
      have := hB rfl
      omega
    rw [hm] at hS
    have h1 := mul_le_mul_of_nonneg_left hS hdn0
    rcases he with rfl | rfl
    · norm_num [mSQ]
      have hcx := mul_nonpos_iff.2 (Or.inl ⟨hc0, hx1⟩)
      have h2 : (d2 - n2) * S0 ≤ (d2 - n2) * (2 * ((c * d1 + d2) - (c * n1 + n2))) := by nlinarith
      have := le_of_mul_le_mul_left h2 (by omega)
      linarith
    · norm_num [mSQ]
      have hcx := mul_le_mul_of_nonneg_left hx0 hc0
      have h2 : (d2 - n2) * S0 < (d2 - n2) * (2 * ((c * d1 + d2) - (c * n1 + n2)) + 2 * c) := by nlinarith
      have := lt_of_mul_lt_mul_left h2 (by omega)
      linarith
  · have hm : min 0 (min (d2 - n2) (3 * n2 - d2)) = 0 := by
      have := hA rfl
      omega
    rw [hm] at hS
    have h1 := mul_le_mul_of_nonneg_left hS hsn0
    rcases he with rfl | rfl
    · norm_num [mSQ]
      by_cases hy : y = 0
      · subst hy
        have : S0 = ((c * d1 + d2) + (c * n1 + n2)) * x := by rw [← hS0]; ring
        nlinarith [mul_nonpos_iff.2 (Or.inl ⟨hsn0, hx1⟩)]
      · have hcy := mul_le_mul_of_nonneg_left (show 1 ≤ y by omega) hc0
        have h2 : (d2 + n2) * S0 < (d2 + n2) * ((c * d1 + d2) + (c * n1 + n2)) := by nlinarith
        have := lt_of_mul_lt_mul_left h2 (by omega)
        linarith
    · norm_num [mSQ]
      have hcy := mul_le_mul_of_nonneg_left hy1 hc0
      have h2 : (d2 + n2) * S0 ≤ (d2 + n2) * ((c * d1 + d2) + (c * n1 + n2) + 2 * c) := by nlinarith
      have := le_of_mul_le_mul_left h2 (by omega)
      linarith

end FLatticePaper.Tiles.H3Bounds
