import FLattice.Auxiliary.PlusEvenProfile

/-!
# Corrected even-plus representative evaluations

These lemmas evaluate `representativeHeight`, including both low-row
overrides. They do not identify any value with the global physical profile:
that requires the separate Euclidean reduction and affine-period lemmas.
All scalar indices are integers and all bounds used below are explicit.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.PlusEvenProfile

open PlusEvenBulk

/-- The `00` representative has no exceptional correction. -/
theorem height_00_eq (r s : ℤ) : representativeHeight 0 0 r s = u00 r s := rfl

/-- The `01` representative has no exceptional correction. -/
theorem height_01_eq (r s : ℤ) : representativeHeight 0 1 r s = u01 r s := rfl

/-- The `10` representative includes the prescribed value at `(0,0)`. -/
theorem height_10_eq (r s : ℤ) : representativeHeight 1 0 r s =
    if r = 0 ∧ s = 0 then 0 else u10 r s := rfl

/-- The `11` representative includes its exceptional value at `(0,0)`. -/
theorem height_11_eq (r s : ℤ) : representativeHeight 1 1 r s =
    if r = 0 ∧ s = 0 then -1 else u11 r s := rfl

private theorem hinge_00_nonpos (a : ℤ) (ha : a ≤ 0) : h00 a = 0 := by
  unfold h00
  omega

private theorem hinge_01_le_one (a : ℤ) (ha : a ≤ 1) : h01 a = 0 := by
  unfold h01
  omega

private theorem hinge_11_le_one (a : ℤ) (ha : a ≤ 1) : h11 a = 0 := by
  unfold h11
  omega

private theorem hinge_00_ge_three (a : ℤ) (ha : 3 ≤ a) : h00 a = 2 * a - 2 := by
  unfold h00
  omega

private theorem hinge_01_ge_three (a : ℤ) (ha : 3 ≤ a) : h01 a = 2 * a - 3 := by
  unfold h01
  omega

private theorem hinge_11_ge_four (a : ℤ) (ha : 4 ≤ a) : h11 a = 2 * a - 4 := by
  unfold h11
  omega

/-- The `00` heights in row zero. -/
theorem height_00_row_zero (s : ℤ) (hs : 0 ≤ s) :
    representativeHeight 0 0 0 s = -1 := by
  rw [height_00_eq, u00, hinge_00_nonpos (0 - s) (by omega)]
  decide

/-- The `01` heights in row zero. -/
theorem height_01_row_zero (s : ℤ) (hs : 0 ≤ s) :
    representativeHeight 0 1 0 s = -1 := by
  rw [height_01_eq, u01, hinge_01_le_one (0 - s) (by omega)]
  decide

/-- Row zero of `10`, retaining the corrected value at the origin. -/
theorem height_10_row_zero (s : ℤ) (hs : 0 ≤ s) :
    representativeHeight 1 0 0 s = if s = 0 then 0 else -2 := by
  rw [height_10_eq]
  simp only [true_and, u10, h10, hinge_01_le_one (0 - s) (by omega)]
  rfl

/-- Row zero of `11`, retaining the corrected value at the origin. -/
theorem height_11_row_zero (s : ℤ) (hs : 0 ≤ s) :
    representativeHeight 1 1 0 s = if s = 0 then -1 else -2 := by
  rw [height_11_eq]
  simp only [true_and, u11, hinge_11_le_one (0 - s) (by omega)]
  rfl

/-- The sole change in row one of `00` occurs at `s=0`. -/
theorem height_00_row_one (s : ℤ) (hs : 0 ≤ s) :
    representativeHeight 0 0 1 s = if s = 0 then -1 else -2 := by
  rw [height_00_eq, u00]
  by_cases h : s = 0
  · subst s
    decide
  · rw [hinge_00_nonpos (1 - s) (by omega), if_neg h]
    decide

/-- Row one of `01`. -/
theorem height_01_row_one (s : ℤ) (hs : 0 ≤ s) :
    representativeHeight 0 1 1 s = -2 := by
  rw [height_01_eq, u01, hinge_01_le_one (1 - s) (by omega)]
  decide

/-- Row one of `10`. -/
theorem height_10_row_one (s : ℤ) (hs : 0 ≤ s) :
    representativeHeight 1 0 1 s = -2 := by
  rw [height_10_eq]
  simp only [Int.one_ne_zero, false_and, if_false, u10, h10]
  rw [hinge_01_le_one (1 - s) (by omega)]
  decide

/-- Row one of `11`. -/
theorem height_11_row_one (s : ℤ) (hs : 0 ≤ s) :
    representativeHeight 1 1 1 s = -2 := by
  rw [height_11_eq]
  simp only [Int.one_ne_zero, false_and, if_false, u11]
  rw [hinge_11_le_one (1 - s) (by omega)]
  decide

/-- The representative used when the physical point `(-1,0)` is reduced. -/
theorem height_01_upper_left (m : ℤ) :
    representativeHeight 0 1 (m + 1) (m - 2) = -(m ^ 2) - 2 * m + 1 := by
  rw [height_01_eq, u01]
  rw [show m + 1 - (m - 2) = 3 by omega]
  have h : h01 3 = 3 := by decide
  rw [h]
  ring

/-- The representative used when the physical point `(0,2)` is reduced. -/
theorem height_00_upper_left (m : ℤ) :
    representativeHeight 0 0 m (m - 1) = -(m ^ 2) := by
  rw [height_00_eq, u00]
  rw [show m - (m - 1) = 1 by omega]
  have h : h00 1 = 1 := by decide
  rw [h]
  ring

/-- The representatives used to reduce `(2s,2)` for the remaining strip sites. -/
theorem height_00_upper_row (m s : ℤ) (hsm : s ≤ m - 1) :
    representativeHeight 0 0 (m + 1) (s - 1) = -(m ^ 2) - 2 * s := by
  rw [height_00_eq, u00, hinge_00_ge_three (m + 1 - (s - 1)) (by omega)]
  ring

/-- The first `00` representative on the left seam above the two low rows. -/
theorem height_00_left_two : representativeHeight 0 0 2 0 = -2 := by decide

/-- The remaining `00` representatives on the left seam. -/
theorem height_00_left (r : ℤ) (hr : 3 ≤ r) :
    representativeHeight 0 0 r 0 = -(r ^ 2) + 2 * r - 3 := by
  rw [height_00_eq, u00, hinge_00_ge_three (r - 0) (by omega)]
  ring

/-- The right incoming representative of a `00` left-seam center. -/
theorem height_01_left (r : ℤ) (hr : 3 ≤ r) :
    representativeHeight 0 1 r 0 = -(r ^ 2) + 2 * r - 4 := by
  rw [height_01_eq, u01, hinge_01_ge_three (r - 0) (by omega)]
  ring

/-- The wrapped left incoming representative of a `00` left-seam center. -/
theorem height_01_wrapped_left (m r : ℤ) (hrm : r ≤ m + 1) :
    representativeHeight 0 1 (r - 1) (m - 1) = -(r ^ 2) + 2 * r - 2 := by
  rw [height_01_eq, u01, hinge_01_le_one (r - 1 - (m - 1)) (by omega)]
  ring

/-- The `11` last-column representative before the exceptional top endpoint. -/
theorem height_11_right (m r : ℤ) (hr : 2 ≤ r) (hrm : r ≤ m) :
    representativeHeight 1 1 r (m - 1) = -(r ^ 2) + r - 2 := by
  rw [height_11_eq, if_neg (by omega), u11,
    hinge_11_le_one (r - (m - 1)) (by omega)]
  ring

/-- The left incoming representative of a last-column `11` center. -/
theorem height_10_right (m r : ℤ) (hr : 2 ≤ r) (hrm : r ≤ m) :
    representativeHeight 1 0 r (m - 1) = -(r ^ 2) + r - 2 := by
  rw [height_10_eq, if_neg (by omega), u10, h10,
    hinge_01_le_one (r - (m - 1)) (by omega)]
  ring

/-- The right incoming representative of a last-column `11` center. -/
theorem height_10_wrapped_right (r : ℤ) (hr : 2 ≤ r) :
    representativeHeight 1 0 (r + 1) 0 = -(r ^ 2) + r - 3 := by
  rw [height_10_eq, if_neg (by omega), u10, h10,
    hinge_01_ge_three (r + 1 - 0) (by omega)]
  ring

/-- The exceptional top endpoint's `11` representative value. -/
theorem height_11_upper_left (m : ℤ) :
    representativeHeight 1 1 (m + 1) (m - 2) = -(m ^ 2) - m + 1 := by
  rw [height_11_eq, if_neg (by omega), u11]
  rw [show m + 1 - (m - 2) = 3 by omega]
  have h : h11 3 = 3 := by decide
  rw [h]
  ring

/-- The `10` representative adjacent to the exceptional top endpoint. -/
theorem height_10_upper_left (m : ℤ) :
    representativeHeight 1 0 (m + 1) (m - 2) = -(m ^ 2) - m + 1 := by
  rw [height_10_eq, if_neg (by omega), u10, h10]
  rw [show m + 1 - (m - 2) = 3 by omega]
  have h : h01 3 = 3 := by decide
  rw [h]
  ring

/-- The `01` top row, throughout its representative range. -/
theorem height_01_top (m s : ℤ) (hsm : s ≤ m - 2) :
    representativeHeight 0 1 (m + 1) s = -(m ^ 2) - 2 * s - 3 := by
  rw [height_01_eq, u01, hinge_01_ge_three (m + 1 - s) (by omega)]
  ring

/-- The `11` top row before its last representative. -/
theorem height_11_top (m s : ℤ) (hsm : s ≤ m - 3) :
    representativeHeight 1 1 (m + 1) s = -(m ^ 2) + m - 2 * s - 4 := by
  rw [height_11_eq, if_neg (by omega), u11,
    hinge_11_ge_four (m + 1 - s) (by omega)]
  ring

/-- The final `01` representative of row `m`. -/
theorem height_01_penultimate_right (m : ℤ) :
    representativeHeight 0 1 m (m - 1) = -(m ^ 2) - 1 := by
  rw [height_01_eq, u01, hinge_01_le_one (m - (m - 1)) (by omega)]
  ring

end FLattice.Auxiliary.PlusEvenProfile
