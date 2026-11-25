import FLatticePaper.Plane.Induction.TwosLaplacianTile

/-! Twos flatness, black centres, odd sites: the black set of the twos field at an odd native site, in coordinates.

At an odd native site `(x, y)` (so `x + y` odd) the quarter turn is even, and the charge is `-1` exactly when the ladder
predicate `LadderOddEvenBlack` holds at the turned point `(2a - y, x + 1)`. That predicate is the three explicit lines
`y = 2a-1, 0 ≤ x ≤ a-2`, `y = a-1, 2 ≤ x ≤ a`, `y - x = a-1, 1 ≤ x ≤ a-1`. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The counterclockwise quarter turn about `(2a, 1)`. -/
theorem rot_twos_ccw (a x y : ℤ) :
    QuarterTurn.counterclockwise.mapSite (2 * a, 1) (x, y) = (2 * a - y, x + 1) := by
  apply Prod.ext <;> (dsimp [QuarterTurn.mapSite, QuarterTurn.turn]; try omega)

/-- At an odd native site, the twos charge is `-1` exactly when `LadderOddEvenBlack` holds at the turned point. -/
theorem lap_odd_black_iff (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hp : (x + y) % 2 = 1) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = -1 ↔
      LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
  rw [laplacian_twos_native k hagree hperiod hn]
  simp only [rot_twos_ccw]
  have he : EvenSite (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
    unfold EvenSite
    dsimp only
    omega
  rw [if_pos he]
  by_cases h : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1)
  · simp [h]
  · simp [h]

/-- The odd black set in coordinates: the three explicit lines. -/
theorem odd_black_explicit (a x y : ℤ) :
    LadderOddEvenBlack a (2 * a - y, x + 1) ↔
      ((y = 2 * a - 1 ∧ 0 ≤ x ∧ x ≤ a - 2) ∨ (y = a - 1 ∧ 2 ≤ x ∧ x ≤ a) ∨
        (y - x = a - 1 ∧ 1 ≤ x ∧ x ≤ a - 1)) := by
  simp only [LadderOddEvenBlack]
  constructor <;> intro h <;> omega

end FLatticePaper.TwosEPolicy
