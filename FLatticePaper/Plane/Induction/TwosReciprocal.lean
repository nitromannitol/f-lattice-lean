import FLatticePaper.Plane.Induction.StandardField
import FLatticePaper.Plane.Induction.TwosSheets
import FLatticePaper.Plane.Induction.WordInduction

/-! Task 50, step 1: the reciprocal field `reciprocalField k` (the standard field of `3^k`, child `1/(2k+3)`) in explicit
integer form. For any deck reduction `z = y + combine i j` with `y` in the tile of the near-one staircase `stairEven`,
the field at `z` is the tile value at `y` corrected by the generator period formula:

  2 * R_k(z) = 2 * stairEvenValue(y) + 2 j (-transverseGrade(y) + cV) - T j (j - 1),

with `cV = stairEvenConstantV(2k+3)` and `T = periodDenominator(1/(2k+3))`. The floor of the reduction is any admissible
`(i, j)`; the formula does not depend on the choice (checked numerically on d = 5, 7, 9 in scripts/twos_reciprocal_check.py). -/

namespace FLatticePaper.Induction
open Farey Construction

/-- The explicit integer form of the reciprocal field at a deck reduction of the tile. -/
theorem reciprocalField_reduction (k : ℕ) {z y : Site} {i j : ℤ}
    (hy : y ∈ (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).sites)
    (hred : z = y + (Fraction.mk 1 (2 * (k : ℤ) + 3)).modifiedDeck.combine i j) :
    2 * reciprocalField k z =
      2 * BaseMask.stairEvenValue (2 * (k : ℤ) + 3) y +
        2 * j * (-((Fraction.mk 1 (2 * (k : ℤ) + 3)).transverseGrade y) + stairEvenConstantV (2 * (k : ℤ) + 3)) -
        (Fraction.mk 1 (2 * (k : ℤ) + 3)).periodDenominator * j * (j - 1) := by
  obtain ⟨hagree, hper⟩ := reciprocalField_spec k
  have hden := stairEven_valid_reciprocal k
  have hinterval : (Fraction.mk 1 (2 * (k : ℤ) + 3)).InUnitInterval := by
    have h3 := hden.1
    exact ⟨by dsimp; omega, by change (0 : ℤ) ≤ 1; decide, by dsimp; omega⟩
  have hF : reciprocalField k y = BaseMask.stairEvenValue (2 * (k : ℤ) + 3) y := by
    have h := hagree ⟨y, hy⟩
    rw [BaseMask.stairEven_raw_height] at h
    simpa using h.symm
  have hG := generator_period_formula hinterval hper y i j
  rw [← hred, hF] at hG
  have key : (2 * (reciprocalField k z : ℝ)) =
      2 * ((BaseMask.stairEvenValue (2 * (k : ℤ) + 3) y : ℤ) : ℝ) +
        2 * (j : ℝ) * (-((Fraction.mk 1 (2 * (k : ℤ) + 3)).transverseGrade y : ℝ) +
          (stairEvenConstantV (2 * (k : ℤ) + 3) : ℝ)) -
        ((Fraction.mk 1 (2 * (k : ℤ) + 3)).periodDenominator : ℝ) * (j : ℝ) * ((j : ℝ) - 1) := by
    rw [hG]
    ring
  exact_mod_cast key

/-- The reciprocal field of `3^1` (child `1/5`) at `(-7, 0)`: the tile value at `(3,2)` after the reduction `-2 U`. -/
theorem reciprocalField_one_neg7 : reciprocalField 1 (-7, 0) = -1 := by
  have hy : ((3 : ℤ), (2 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * ((1 : ℕ) : ℤ) + 3)).sites :=
    BaseMask.mem_stairEven_raw_iff.mpr ⟨by norm_num, by norm_num, Or.inr (by norm_num)⟩
  have hred : ((-7 : ℤ), (0 : ℤ)) = ((3 : ℤ), (2 : ℤ)) +
      (Fraction.mk 1 (2 * ((1 : ℕ) : ℤ) + 3)).modifiedDeck.combine (-2) 0 := by
    simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, PeriodDeck.combine, Fraction.unmodifiedDeck]
  have h := reciprocalField_reduction 1 hy hred
  have hval : BaseMask.stairEvenValue (2 * ((1 : ℕ) : ℤ) + 3) (3, 2) = -1 := by
    norm_num [BaseMask.stairEvenValue, BaseMask.StairEvenCorner]
  rw [hval] at h
  norm_num [Fraction.periodDenominator, Fraction.transverseGrade, stairEvenConstantV, chooseTwo] at h
  linarith

/-- The reciprocal field of `3^1` at `(-6, 1)`: the tile value at `(-1,2)` after the reduction `-U`. -/
theorem reciprocalField_one_neg6_1 : reciprocalField 1 (-6, 1) = -3 := by
  have hy : ((-1 : ℤ), (2 : ℤ)) ∈ (BaseMask.stairEven.raw (2 * ((1 : ℕ) : ℤ) + 3)).sites :=
    BaseMask.mem_stairEven_raw_iff.mpr ⟨by norm_num, by norm_num, Or.inr (by norm_num)⟩
  have hred : ((-6 : ℤ), (1 : ℤ)) = ((-1 : ℤ), (2 : ℤ)) +
      (Fraction.mk 1 (2 * ((1 : ℕ) : ℤ) + 3)).modifiedDeck.combine (-1) 0 := by
    simp [Fraction.modifiedDeck, Fraction.periodMultiplicity, PeriodDeck.combine, Fraction.unmodifiedDeck]
  have h := reciprocalField_reduction 1 hy hred
  have hval : BaseMask.stairEvenValue (2 * ((1 : ℕ) : ℤ) + 3) (-1, 2) = -3 := by
    norm_num [BaseMask.stairEvenValue, BaseMask.StairEvenCorner]
  rw [hval] at h
  norm_num [Fraction.periodDenominator, Fraction.transverseGrade, stairEvenConstantV, chooseTwo] at h
  linarith

/-- The sheet `A` of the frame of `2^2` at `(2,8)`: the reciprocal field at `(-7,0)` plus `harmonicGrid (1,7) = -12`. -/
theorem twos_sheetA_at_two_eight :
    (frameAt (List.replicate 2 Digit.two)).sheetA
        (quarterTurnField (standardField (conjWord (List.replicate 2 Digit.two)))) (2, 8) = -13 := by
  rw [twos_sheetA, show conjWord (List.replicate 2 Digit.two) = List.replicate 1 Digit.three from
    conjWord_replicate_two 1, standardField_threes, quarterTurnField_eq]
  have hR := reciprocalField_one_neg7
  have hH : harmonicGrid ((2 : ℤ) - 1, (8 : ℤ) - 1) = -12 := by
    norm_num [harmonicGrid]
  show reciprocalField 1 (-((2 : ℤ) - 1, (8 : ℤ) - 1).2, ((2 : ℤ) - 1, (8 : ℤ) - 1).1 - 1) +
      harmonicGrid ((2 : ℤ) - 1, (8 : ℤ) - 1) = -13
  have e : (-((2 : ℤ) - 1, (8 : ℤ) - 1).2, ((2 : ℤ) - 1, (8 : ℤ) - 1).1 - 1) = (-7, 0) := by
    norm_num
  rw [e, hR, hH]
  norm_num

/-- The sheet `C` of the frame of `2^2` at `(2,8)`: the reciprocal field at `(-6,1)` plus `harmonicGrid (2,6) - 6`. -/
theorem twos_sheetC_at_two_eight :
    (frameAt (List.replicate 2 Digit.two)).sheetC
        (quarterTurnField (standardField (conjWord (List.replicate 2 Digit.two)))) (2, 8) = -14 := by
  rw [twos_sheetC, show conjWord (List.replicate 2 Digit.two) = List.replicate 1 Digit.three from
    conjWord_replicate_two 1, standardField_threes, quarterTurnField_eq]
  have hR := reciprocalField_one_neg6_1
  have hH : harmonicGrid ((2 : ℤ), (8 : ℤ) - 2) = -5 := by
    norm_num [harmonicGrid]
  show reciprocalField 1 (-((2 : ℤ), (8 : ℤ) - 2).2, ((2 : ℤ), (8 : ℤ) - 2).1 - 1) +
      harmonicGrid ((2 : ℤ), (8 : ℤ) - 2) + ((2 : ℤ) - 8) = -14
  have e : (-((2 : ℤ), (8 : ℤ) - 2).2, ((2 : ℤ), (8 : ℤ) - 2).1 - 1) = (-6, 1) := by
    norm_num
  rw [e, hR, hH]
  norm_num

end FLatticePaper.Induction
