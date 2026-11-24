import FLatticePaper.Plane.Induction.ReciprocalIncrements

/-! The closed polygon of the pure frame `3^k` lies in the native raw tile `RawMem`.

With `d` odd, `T = d² + 2d − 1`, `t = x − d y` (tGrade) and `s = (d+1) x + (d−1) y` (sGrade), the identity
`T y = s − (d+1) t` bounds `y`, and the remaining coordinates follow from the two grade bounds and parity.
Only the inclusion `polygon ⊆ raw` is needed (for the price and slip ranges). -/

namespace FLatticePaper.Induction

/-- The even branch of the closed polygon lies in the raw tile. -/
theorem polygon_even_raw (d x y : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1) (hpar : (x + y) % 2 = 0)
    (h1 : 2 - (d * d + 2 * d - 1) ≤ x - d * y) (h2 : x - d * y ≤ d - 1)
    (h3 : 0 ≤ (d + 1) * x + (d - 1) * y) (h4 : (d + 1) * x + (d - 1) * y ≤ d * d + 2 * d - 1 + 2) :
    RawMem d x y := by
  have hT : 0 < d * d + 2 * d - 1 := by nlinarith
  have key : (d * d + 2 * d - 1) * y = ((d + 1) * x + (d - 1) * y) - (d + 1) * (x - d * y) := by ring
  have hy0 : 0 ≤ y := by
    by_contra hneg
    have hy' : y ≤ -1 := by omega
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ d + 1) (by linarith : (0:ℤ) ≤ d - 1 - (x - d * y)),
      mul_nonneg hT.le (by linarith : (0:ℤ) ≤ -1 - y)]
  have hy1 : y ≤ d + 1 := by
    by_contra hbig
    have hy' : d + 2 ≤ y := by omega
    nlinarith [mul_nonneg hT.le (by linarith : (0:ℤ) ≤ y - (d + 2)),
      mul_nonneg (by linarith : (0:ℤ) ≤ d + 1) (by linarith : (0:ℤ) ≤ (x - d * y) - (2 - (d * d + 2 * d - 1)))]
  have hx1 : x ≤ d := by
    by_contra hbig
    have hx' : d + 1 ≤ x := by omega
    rcases eq_or_lt_of_le hy0 with h0 | hpos
    · subst h0
      nlinarith
    · nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ d + 1) (by linarith : (0:ℤ) ≤ x - (d + 1)),
        mul_nonneg (by linarith : (0:ℤ) ≤ d - 1) (by linarith : (0:ℤ) ≤ y - 1)]
  have hx2 : 2 - d ≤ x := by
    rcases (show y ≤ d ∨ y = d + 1 by omega) with hy | hy
    · by_contra hsmall
      have hx' : x ≤ 1 - d := by omega
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ d + 1) (by linarith : (0:ℤ) ≤ 1 - d - x),
        mul_nonneg (by linarith : (0:ℤ) ≤ d - 1) (by linarith : (0:ℤ) ≤ d - y)]
    · subst hy
      nlinarith
  have hdiag : (x = 0 ∧ y = 0) ∨ (x = 2 ∧ y = d + 1) ∨ (1 ≤ x + y ∧ x + y ≤ d + 2) := by
    by_cases hA : x + y ≤ d + 2
    · by_cases hB : 1 ≤ x + y
      · exact Or.inr (Or.inr ⟨hB, hA⟩)
      · have hz : x + y ≤ 0 := by omega
        have hy00 : y = 0 := by
          nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ d + 1) (by linarith : (0:ℤ) ≤ -(x + y))]
        have hx00 : x = 0 := by
          subst hy00
          have hxnn : 0 ≤ x := by
            by_contra hneg
            have hneg' : x ≤ -1 := by omega
            nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ d + 1) (by linarith : (0:ℤ) ≤ -1 - x)]
          omega
        exact Or.inl ⟨hx00, hy00⟩
    · have hyd : y = d + 1 := by
        nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ d + 1) (by linarith : (0:ℤ) ≤ x + y - (d + 3))]
      subst hyd
      have hx2' : x = 2 := by nlinarith
      exact Or.inr (Or.inl ⟨hx2', rfl⟩)
  exact ⟨⟨hx2, hx1⟩, ⟨hy0, hy1⟩, hdiag⟩

/-- The odd branch of the closed polygon lies in the raw tile (the corners are even, so only the diagonal occurs). -/
theorem polygon_odd_raw (d x y : ℤ) (hd : 3 ≤ d) (hodd : d % 2 = 1) (hpar : (x + y) % 2 = 1)
    (h1 : 1 - (d * d + 2 * d - 1) ≤ x - d * y) (h2 : x - d * y ≤ d)
    (h3 : 3 - d ≤ (d + 1) * x + (d - 1) * y) (h4 : (d + 1) * x + (d - 1) * y ≤ d * d + 2 * d - 1 + d - 1) :
    RawMem d x y := by
  have hT : 0 < d * d + 2 * d - 1 := by nlinarith
  have key : (d * d + 2 * d - 1) * y = ((d + 1) * x + (d - 1) * y) - (d + 1) * (x - d * y) := by ring
  have hy0 : 0 ≤ y := by
    by_contra hneg
    have hy' : y ≤ -1 := by omega
    nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ d + 1) (by linarith : (0:ℤ) ≤ d - (x - d * y)),
      mul_nonneg hT.le (by linarith : (0:ℤ) ≤ -1 - y)]
  have hy1 : y ≤ d + 1 := by
    by_contra hbig
    have hy' : d + 2 ≤ y := by omega
    nlinarith [mul_nonneg hT.le (by linarith : (0:ℤ) ≤ y - (d + 2)),
      mul_nonneg (by linarith : (0:ℤ) ≤ d + 1) (by linarith : (0:ℤ) ≤ (x - d * y) - (1 - (d * d + 2 * d - 1)))]
  have hx1 : x ≤ d := by
    by_contra hbig
    have hx' : d + 1 ≤ x := by omega
    rcases eq_or_lt_of_le hy0 with h0 | hpos
    · subst h0
      nlinarith
    · nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ d + 1) (by linarith : (0:ℤ) ≤ x - (d + 1)),
        mul_nonneg (by linarith : (0:ℤ) ≤ d - 1) (by linarith : (0:ℤ) ≤ y - 1)]
  have hx2 : 2 - d ≤ x := by
    rcases (show y ≤ d ∨ y = d + 1 by omega) with hy | hy
    · by_contra hsmall
      have hx' : x ≤ 1 - d := by omega
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ d + 1) (by linarith : (0:ℤ) ≤ 1 - d - x),
        mul_nonneg (by linarith : (0:ℤ) ≤ d - 1) (by linarith : (0:ℤ) ≤ d - y)]
    · subst hy
      nlinarith
  have hdiag : 1 ≤ x + y ∧ x + y ≤ d + 2 := by
    constructor
    · by_contra hlow
      have hz : x + y ≤ -1 := by omega
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ d + 1) (by linarith : (0:ℤ) ≤ -1 - (x + y))]
    · by_contra hup
      have hz : d + 4 ≤ x + y := by omega
      nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ d + 1) (by linarith : (0:ℤ) ≤ x + y - (d + 4))]
  exact ⟨⟨hx2, hx1⟩, ⟨hy0, hy1⟩, Or.inr (Or.inr hdiag)⟩

end FLatticePaper.Induction
