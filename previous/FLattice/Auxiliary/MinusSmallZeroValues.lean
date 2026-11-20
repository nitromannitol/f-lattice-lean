import FLattice.Auxiliary.MinusSmallSpecialValues
import FLattice.Auxiliary.MinusSmallAverages

/-!
# Literal smallest-minus values and all four remaining averaging contradictions

All fourteen threshold-zero leaves and all ten additional source values are
computed from the actual smallest-minus profile, including signed reductions.
The graph-independent averaging helpers receive derived bounds, never assumed
profile evaluations. The global profile bounds used here are supplied by the
original-coset comparison assembly in a separate module.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.MinusSmallProfile

private theorem zero_value_0 : profile 0 (4) (-1) = (0) := by decide
private theorem zero_value_1 : profile 1 (-3) (-3) = (0) := by decide
private theorem zero_value_2 : profile 0 (5) (1) = (1) := by decide
private theorem zero_value_3 : profile 0 (0) (-3) = (-1) := by decide
private theorem zero_value_4 : profile 1 (-2) (-1) = (1) := by decide
private theorem zero_value_5 : profile 0 (6) (2) = (0) := by decide
private theorem zero_value_6 : profile 0 (0) (-1) = (1) := by decide
private theorem zero_value_7 : profile 0 (6) (3) = (-1) := by decide
private theorem zero_value_8 : profile 0 (7) (3) = (-1) := by decide
private theorem zero_value_9 : profile 0 (6) (5) = (-5) := by decide
private theorem zero_value_10 : profile 1 (-1) (3) = (-3) := by decide
private theorem zero_value_11 : profile 0 (1) (1) = (1) := by decide
private theorem zero_value_12 : profile 0 (2) (3) = (-2) := by decide
private theorem zero_value_13 : profile 0 (1) (0) = (1) := by decide
private theorem extra_value_0 : profile 0 (7) (2) = (-1) := by decide
private theorem extra_value_1 : profile 0 (8) (3) = (-2) := by decide
private theorem extra_value_2 : profile 0 (9) (1) = (-3) := by decide
private theorem extra_value_3 : profile 1 (1) (1) = (0) := by decide
private theorem extra_value_4 : profile 0 (6) (1) = (0) := by decide
private theorem extra_value_5 : profile 0 (7) (3) = (-1) := by decide
private theorem extra_value_6 : profile 1 (-1) (-1) = (1) := by decide
private theorem extra_value_7 : profile 0 (1) (1) = (1) := by decide
private theorem extra_value_8 : profile 0 (2) (-1) = (1) := by decide
private theorem extra_value_9 : profile 1 (0) (1) = (0) := by decide

/-- The three actual lower profiles close the smallest even threshold zero. -/
theorem one_le_origin_of_three_profiles
    (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hOrigin : 0 ≤ h (0, 0))
    (hA : ∀ x y : ℤ, profile 0 (x + 8) (y + 2) ≤ h (x, y))
    (hB : ∀ x y : ℤ, profile 1 (x - 1) y - 1 ≤ h (x, y))
    (hC : ∀ x y : ℤ, profile 0 x y - 1 ≤ h (x, y)) :
    1 ≤ h (0, 0) := by
  apply MinusProfile.one_le_origin_of_fourteen_bounds h hSuperharmonic hOrigin
  · have hBound := hA (-4) (-3)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [zero_value_0] at hBound
    omega
  · have hBound := hB (-2) (-3)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [zero_value_1] at hBound
    omega
  · have hBound := hA (-3) (-1)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [zero_value_2] at hBound
    omega
  · have hBound := hC (0) (-3)
    rw [zero_value_3] at hBound
    omega
  · have hBound := hB (-1) (-1)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [zero_value_4] at hBound
    omega
  · have hBound := hA (-2) (0)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [zero_value_5] at hBound
    omega
  · have hBound := hC (0) (-1)
    rw [zero_value_6] at hBound
    omega
  · have hBound := hA (-2) (1)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [zero_value_7] at hBound
    omega
  · have hBound := hA (-1) (1)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [zero_value_8] at hBound
    omega
  · have hBound := hA (-2) (3)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [zero_value_9] at hBound
    omega
  · have hBound := hB (0) (3)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [zero_value_10] at hBound
    omega
  · have hBound := hC (1) (1)
    rw [zero_value_11] at hBound
    omega
  · have hBound := hC (2) (3)
    rw [zero_value_12] at hBound
    omega
  · have hBound := hC (1) (0)
    rw [zero_value_13] at hBound
    omega

/-- The four smallest even threshold minus-two seeds follow from A+2 and B. -/
theorem one_le_origin_of_even_minus_two_profiles
    (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hA : ∀ x y : ℤ, profile 0 (x + 8) (y + 2) + 2 ≤ h (x, y))
    (hB : ∀ x y : ℤ, profile 1 (x - 1) y - 1 ≤ h (x, y)) :
    1 ≤ h (0, 0) := by
  apply MinusProfile.one_le_origin_of_small_even_minus_two_bounds h hSuperharmonic
  · have hBound := hA (-1) (0)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [extra_value_0] at hBound
    omega
  · have hBound := hA (0) (1)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [extra_value_1] at hBound
    omega
  · have hBound := hA (1) (-1)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [extra_value_2] at hBound
    omega
  · have hBound := hB (2) (1)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [extra_value_3] at hBound
    omega

/-- The five smallest even threshold minus-one seeds follow from A+1, B and E-2. -/
theorem one_le_origin_of_even_minus_one_profiles
    (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hA : ∀ x y : ℤ, profile 0 (x + 8) (y + 2) + 1 ≤ h (x, y))
    (hB : ∀ x y : ℤ, profile 1 (x - 1) y - 1 ≤ h (x, y))
    (hC : ∀ x y : ℤ, profile 0 x y - 2 ≤ h (x, y)) :
    1 ≤ h (0, 0) := by
  apply MinusProfile.one_le_origin_of_small_even_minus_one_bounds h hSuperharmonic
  · have hBound := hA (-2) (-1)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [extra_value_4] at hBound
    omega
  · have hBound := hA (-1) (1)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [extra_value_5] at hBound
    omega
  · have hBound := hB (0) (-1)
    norm_num only [Int.reduceAdd, Int.reduceSub] at hBound
    rw [extra_value_6] at hBound
    omega
  · have hBound := hC (1) (1)
    rw [extra_value_7] at hBound
    omega
  · have hBound := hC (2) (-1)
    rw [extra_value_8] at hBound
    omega

/-- The remaining odd threshold one is excluded by the two actual odd profile bounds. -/
theorem one_le_origin_of_odd_one_profiles
    (h : ℤ × ℤ → ℤ)
    (hSuperharmonic : ∀ x y : ℤ,
      (if (x + y + 1) % 2 = 0 then h (x - 1, y) + h (x + 1, y)
        else h (x, y - 1) + h (x, y + 1)) ≤ 2 * h (x, y))
    (hPlus : ∀ x y : ℤ, profile 1 x y ≤ h (x, y))
    (hMinus : ∀ x y : ℤ, profile 1 (x - 2) y - 1 ≤ h (x, y)) :
    1 ≤ h (0, 0) := by
  apply MinusProfile.one_le_origin_of_small_odd_one_bounds h hSuperharmonic
  · have hBound := hPlus (-1) (-1)
    rw [extra_value_6] at hBound
    exact hBound
  · have hBound := hPlus 0 1
    rw [extra_value_9] at hBound
    exact hBound
  · have hBound := hMinus 1 (-1)
    norm_num only [Int.reduceSub] at hBound
    rw [extra_value_6] at hBound
    omega

end FLattice.Auxiliary.MinusSmallProfile
