import FLattice.Auxiliary.MatrixCoordinates
import Mathlib.Algebra.Order.Floor.Ring

/-!
# A fundamental diamond and its radial boundary

Rounding in the two rotated coordinates places every point in a translate
of the unit diamond by an actual integer harmonic peak. A radial boundary
point then gives a strictly smaller matrix whenever the trace lies above
the downward cone. No nearest-point or Voronoi theorem is used.
-/

set_option autoImplicit false

namespace FLattice.Auxiliary.FundamentalDiamond

open MatrixCoordinates

private theorem abs_add_abs_le_of_sum_diff (a b : ℝ)
    (hSum : |a + b| ≤ 1) (hDiff : |a - b| ≤ 1) : |a| + |b| ≤ 1 := by
  obtain ⟨hSumLower, hSumUpper⟩ := abs_le.mp hSum
  obtain ⟨hDiffLower, hDiffUpper⟩ := abs_le.mp hDiff
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  · rw [abs_of_nonneg ha, abs_of_nonneg hb]
    exact hSumUpper
  · rw [abs_of_nonneg ha, abs_of_neg (lt_of_not_ge hb)]
    linarith only [hDiffUpper]
  · rw [abs_of_neg (lt_of_not_ge ha), abs_of_nonneg hb]
    linarith only [hDiffLower]
  · rw [abs_of_neg (lt_of_not_ge ha), abs_of_neg (lt_of_not_ge hb)]
    linarith only [hSumLower]

/-- Every traceless-coordinate point lies in an actual peak translate
of the closed unit diamond. The integer center is obtained by rounding. -/
theorem exists_peak_translate (a b : ℝ) :
    ∃ s t : ℤ,
      |a - ((s : ℝ) - (t : ℝ))| + |b - ((s : ℝ) + (t : ℝ))| ≤ 1 := by
  let s : ℤ := ⌊(a + b + 1) / 2⌋
  let t : ℤ := ⌊(b - a + 1) / 2⌋
  have hsLower := Int.floor_le ((a + b + 1) / 2)
  have hsUpper := Int.lt_floor_add_one ((a + b + 1) / 2)
  have htLower := Int.floor_le ((b - a + 1) / 2)
  have htUpper := Int.lt_floor_add_one ((b - a + 1) / 2)
  refine ⟨s, t, abs_add_abs_le_of_sum_diff _ _ ?_ ?_⟩
  · apply abs_le.mpr
    dsimp [s, t]
    constructor <;> linarith only [hsLower, hsUpper]
  · apply abs_le.mpr
    dsimp [s, t]
    constructor <;> linarith only [htLower, htUpper]

/-- Above the cone in the first-quadrant part of the diamond, an actual
radial boundary reference is strictly dominated. -/
theorem exists_positive_edge_difference (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hSum : a + b ≤ 1) (hc : -radius a b < c) :
    ∃ u v : ℝ, 0 ≤ u ∧ 0 ≤ v ∧ u + v = 1 ∧
      (matrix a b c - matrix u v (-radius u v)).PosDef := by
  by_cases hZero : a + b = 0
  · have haZero : a = 0 := by linarith
    have hbZero : b = 0 := by linarith
    subst a
    subst b
    refine ⟨1, 0, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [matrix_sub]
    apply posDef_of_radius_lt
    norm_num [radius] at hc ⊢
    linarith only [hc]
  · have hPositive : 0 < a + b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hZero)
    let t : ℝ := 1 / (a + b)
    have ht : 0 < t := by dsimp [t]; positivity
    have htOne : 1 ≤ t := by
      dsimp [t]
      exact (le_div_iff₀ hPositive).mpr (by simpa only [one_mul] using hSum)
    have hEdge : t * a + t * b = 1 := by dsimp [t]; field_simp
    refine ⟨t * a, t * b, mul_nonneg (le_of_lt ht) ha,
      mul_nonneg (le_of_lt ht) hb, hEdge, ?_⟩
    rw [matrix_sub]
    apply posDef_of_radius_lt
    have hBoundary : radius (t * a) (t * b) = t * radius a b := by
      rw [radius_smul, abs_of_pos ht]
    have hDifference : radius (a - t * a) (b - t * b) = (t - 1) * radius a b := by
      have hA : a - t * a = (1 - t) * a := by ring
      have hB : b - t * b = (1 - t) * b := by ring
      rw [hA, hB, radius_smul, abs_of_nonpos (by linarith : 1 - t ≤ 0)]
      ring
    rw [hBoundary, hDifference]
    linarith only [hc]

end FLattice.Auxiliary.FundamentalDiamond
