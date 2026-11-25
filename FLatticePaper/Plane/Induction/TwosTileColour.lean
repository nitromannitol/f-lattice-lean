import FLatticePaper.Plane.Induction.TwosLaplacianTile

/-! The colour of a native point of the twos field: `laplacian F (x, y) = −1` exactly on the black predicate `TwosBlackP`, and `0`
otherwise (the charge table of `laplacian_twos_native` at the quarter turn `(2a − y, x + 1)`). -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- The black sites of the twos field at a native point `(x, y)` with `a = 2k+4`: the charge table at `q = (2a − y, x + 1)`. -/
def TwosBlackP (a x y : ℤ) : Prop :=
  (EvenSite (2 * a - y, x + 1) ∧ LadderOddEvenBlack a (2 * a - y, x + 1)) ∨
    (¬ EvenSite (2 * a - y, x + 1) ∧ ¬ LadderOddOddWhite a (2 * a - y, x + 1))

theorem tile_colour (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {x y : ℤ} (hu : NativeT (2 * (k : ℤ) + 4) x y) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) =
      if TwosBlackP (2 * (k : ℤ) + 4) x y then -1 else 0 := by
  have h := laplacian_twos_native k hagree hperiod (u := (x, y)) hu
  rw [quarterTurn_offset_apply] at h
  dsimp only at h
  rw [h]
  unfold TwosBlackP
  by_cases he : EvenSite (2 * (2 * (k : ℤ) + 4) - y, x + 1) <;>
    by_cases hb : LadderOddEvenBlack (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1) <;>
    by_cases hw : LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1) <;>
    simp [he, hb, hw]

end FLatticePaper.TwosEPolicy
