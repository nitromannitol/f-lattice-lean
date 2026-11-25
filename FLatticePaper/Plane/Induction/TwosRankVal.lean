import FLatticePaper.Plane.Induction.TwosEPolicy

/-! Twos flatness, the closed values of the rank on each region of `(h, y)`, with `h = y - x` (sign `+1`). The bulk value
`bulkR` has four regions (`h ≤ a-2` or `h ≥ a`, and `y` below or above the middle row), the middle column `h = a-1`, and the
first column `h = -1`; the free values `freeH`, `freeV` split by the free classes. Each lemma is a single unfolding and split. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

theorem bulk_low_lo {a x y : ℤ} (hl : y - x ≤ a - 2) (hm : y - x ≠ -1) (hy : y ≤ a - 1) :
    bulkR a 1 x y = 2 * y - (x + y) % 2 := by
  simp only [bulkR]
  split_ifs <;> first | exact False.elim ‹False› | omega

theorem bulk_low_hi {a x y : ℤ} (hl : y - x ≤ a - 2) (hm : y - x ≠ -1) (hy : a - 1 ≤ y) :
    bulkR a 1 x y = 4 * a - 4 - 2 * y - (x + y) % 2 := by
  simp only [bulkR]
  split_ifs <;> first | exact False.elim ‹False› | omega

theorem bulk_high_lo {a x y : ℤ} (ha : 4 ≤ a) (hl : a ≤ y - x) (hy : y ≤ 2 * a - 1) :
    bulkR a 1 x y = 2 * y - 2 * a + 2 - (x + y) % 2 := by
  simp only [bulkR]
  split_ifs <;> first | exact False.elim ‹False› | omega

theorem bulk_high_hi {a x y : ℤ} (ha : 4 ≤ a) (hl : a ≤ y - x) (hy : 2 * a - 1 ≤ y) :
    bulkR a 1 x y = 6 * a - 2 - 2 * y - (x + y) % 2 := by
  simp only [bulkR]
  split_ifs <;> first | exact False.elim ‹False› | omega

theorem bulk_mid {a x y : ℤ} (ha : 4 ≤ a) (hl : y - x = a - 1) : bulkR a 1 x y = 2 * x + 3 := by
  simp only [bulkR]
  split_ifs <;> first | exact False.elim ‹False› | omega

theorem bulk_first {a x y : ℤ} (hl : y - x = -1) :
    bulkR a 1 x y = (if x = a then 2 * a - 3 else 2 * a + 1 - 2 * y) := by
  simp only [bulkR]
  split_ifs <;> first | exact False.elim ‹False› | omega

theorem freeH_one {a x y : ℤ} (hx : x = 1) : freeH a 1 x y = 2 * a + 1 := by
  simp only [freeH]
  split_ifs <;> first | exact False.elim ‹False› | omega

theorem freeH_mid {a x y : ℤ} (h2 : 2 ≤ x) (h3 : x ≤ a) : freeH a 1 x y = 2 * (a + 1 - x) := by
  simp only [freeH]
  split_ifs <;> first | exact False.elim ‹False› | omega

theorem freeH_last {a x y : ℤ} (h : x = a + 1) (ha : 4 ≤ a) : freeH a 1 x y = 1 := by
  simp only [freeH]
  split_ifs <;> first | exact False.elim ‹False› | omega

theorem freeV_lo {a x y : ℤ} (h : y < a) : freeV a 1 x y = 2 * y - y % 2 := by
  simp only [freeV]
  split_ifs <;> first | exact False.elim ‹False› | omega

theorem freeV_hi {a x y : ℤ} (h : a ≤ y) : freeV a 1 x y = 2 * (y - a) + 1 + (y - a) % 2 := by
  simp only [freeV]
  split_ifs <;> first | exact False.elim ‹False› | omega

end FLatticePaper.TwosEPolicy
