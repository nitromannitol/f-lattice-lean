import FLatticePaper.Plane.Induction.TwosPeriods

/-! Task 72 / twos base: the explicit values of the standard field of `2^(k+1)`, the analogue of
`TwosReciprocal.reciprocalField_reduction`.

`standardField (2^(k+1))` equals the near-one doubled-staircase height `paperNearLadderValue (2k+4) (z₁, z₂ + 1)` on the closed
polygon `E` of `2^(k+1)` (`twos_standardField_eq_rotate` and `rotate_eq_on_E`, with the ladder extension `S` of
`ladderOdd_exists_extension`; no hypothesis is left). The archive's native domain of the doubled ladder lies in `E`, and its chart is the
identity (`F_arch(x, y) = paperNearLadderValue (2K+2) (x, y + 1)` with `K = k + 1`).

`twos_standardField_reduction` gives every value from its representative in `E` and the generator period formula, with the period
constants `(0, ladderEvenConstantV (2k+4))` of `twos_standardField_periods`. -/

namespace FLatticePaper.Induction
open Farey Construction

/-- **The closed form of the twos standard field on its closed polygon.** -/
theorem standardField_twos_eq_paperNear (k : ℕ) {z : Site}
    (hz : z ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon) :
    standardField (List.replicate (k + 1) Digit.two) z =
      paperNearLadderValue (2 * (k : ℤ) + 4) (z.1, z.2 + 1) := by
  have hvalid : BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) := ⟨by omega, by omega⟩
  obtain ⟨S, hagree, hperiod, -⟩ := ladderOdd_exists_extension hvalid
  rw [twos_standardField_eq_rotate k hagree hperiod z, rotate_eq_on_E k hagree hperiod hz]

/-- **The explicit deck reduction of the twos standard field.** For a representative `y` in the closed polygon and a deck vector
`z = y + combine i j`: `2 F(z) = 2 P(y) + 2 j (−t(y) + cV) − T j (j − 1)`, with `P` the near-one height at `y + (0, 1)`. -/
theorem standardField_twos_reduction (k : ℕ) {z y : Site} {i j : ℤ}
    (hy : y ∈ (frameAt (List.replicate (k + 1) Digit.two)).closedPolygon)
    (hred : z = y + (frameAt (List.replicate (k + 1) Digit.two)).child.modifiedDeck.combine i j) :
    2 * standardField (List.replicate (k + 1) Digit.two) z =
      2 * paperNearLadderValue (2 * (k : ℤ) + 4) (y.1, y.2 + 1) +
        2 * j * (-((frameAt (List.replicate (k + 1) Digit.two)).child.transverseGrade y) +
          ladderEvenConstantV (2 * (k : ℤ) + 4)) -
        (frameAt (List.replicate (k + 1) Digit.two)).child.periodDenominator * j * (j - 1) := by
  have hvalid : BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) := ⟨by omega, by omega⟩
  obtain ⟨S, hagree, hperiod, -⟩ := ladderOdd_exists_extension hvalid
  have hF := twos_standardField_periods k hagree hperiod
  have hinterval : (frameAt (List.replicate (k + 1) Digit.two)).child.InUnitInterval :=
    ((frameAt (List.replicate (k + 1) Digit.two)).valid.current_interior .even).inUnitInterval
  have hval := standardField_twos_eq_paperNear k hy
  have hG := generator_period_formula hinterval hF y i j
  rw [← hred, hval] at hG
  have key : (2 * (standardField (List.replicate (k + 1) Digit.two) z : ℝ)) =
      2 * ((paperNearLadderValue (2 * (k : ℤ) + 4) (y.1, y.2 + 1) : ℤ) : ℝ) +
        2 * (j : ℝ) * (-((frameAt (List.replicate (k + 1) Digit.two)).child.transverseGrade y : ℝ) +
          (ladderEvenConstantV (2 * (k : ℤ) + 4) : ℝ)) -
        ((frameAt (List.replicate (k + 1) Digit.two)).child.periodDenominator : ℝ) * (j : ℝ) * ((j : ℝ) - 1) := by
    rw [hG]
    push_cast
    ring
  exact_mod_cast key

end FLatticePaper.Induction
