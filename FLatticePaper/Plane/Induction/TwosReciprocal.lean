import FLatticePaper.Plane.Induction.StandardField

/-! Task 50, step 1: the reciprocal field `reciprocalField k` (the standard field of `3^k`, child `1/(2k+3)`) in explicit
integer form. For any deck reduction `z = y + combine i j` with `y` in the tile of the near-one staircase `stairEven`,
the field at `z` is the tile value at `y` corrected by the generator period formula:

  2 * R_k(z) = 2 * stairEvenValue(y) + 2 j (-transverseGrade(y) + cV) - T j (j - 1),

with `cV = stairEvenConstantV(2k+3)` and `T = periodDenominator(1/(2k+3))`. The floor of the reduction is any admissible
`(i, j)`; the formula does not depend on the choice (checked numerically on d = 5, 7, 9 in scripts/twos_reciprocal_check.py). -/

namespace FLatticePaper.Induction
open Farey Construction

theorem reciprocalField_spec (k : ℕ) :
    (BaseMask.stairEven.raw (2 * (k : ℤ) + 3)).Agrees (reciprocalField k) 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 3)) (reciprocalField k) 0
        (stairEvenConstantV (2 * (k : ℤ) + 3)) := by
  have h := Classical.choose_spec
    (stairEven_exists_extension (den := 2 * (k : ℤ) + 3) (stairEven_valid_reciprocal k))
  exact ⟨h.1, h.2.1⟩

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

end FLatticePaper.Induction
