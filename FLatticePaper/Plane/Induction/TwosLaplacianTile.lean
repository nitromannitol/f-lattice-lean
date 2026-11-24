import FLatticePaper.Plane.Induction.TwosNearOne
import FLatticePaper.Plane.Induction.TwosPeriods
import FLatticePaper.Plane.Induction.TwosEPolicy
import FLatticePaper.Construction.LadderLaplacian

/-! The Laplacian of the twos field on the native box (task 72). The twos standard field is the rotated odd-ladder source
(`twos_standardField_eq_rotate`), and its Laplacian at `u` is the source Laplacian at the quarter turn `(2a - u.2, u.1 + 1)`
(`rotateLadderField_laplacian`). The native box `FLatticePaper.TwosEPolicy.NativeT` is exactly the set of `u` whose quarter
turn is a raw site of the odd-ladder mask, so the charge table `ladderOdd_laplacian_on_raw` applies at every native point. -/

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey

/-- The odd-ladder source at the denominator `a = 2k+4` is valid. -/
theorem ladderOdd_valid_twos (k : ℕ) : BaseMask.ladderOdd.Valid (2 * (k : ℤ) + 4) :=
  ⟨by omega, by omega⟩

/-- The twos standard field's Laplacian at `u` is the source Laplacian at the quarter turn of `u`. -/
theorem laplacian_twos_eq_source (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    (u : Site) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) u =
      laplacian S (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) u) := by
  have hfun : standardField (List.replicate (k + 1) Digit.two) =
      rotateLadderField (2 * (k : ℤ) + 4) S :=
    funext fun z => twos_standardField_eq_rotate k hagree hperiod z
  rw [hfun, rotateLadderField_laplacian]

/-- The quarter turn of a native point is a raw site of the odd-ladder mask. -/
theorem nativeT_rot_raw {a : ℤ} (ha : 4 ≤ a) {u : Site} (hu : NativeT a u.1 u.2) :
    QuarterTurn.counterclockwise.mapSite (2 * a, 1) u ∈ (BaseMask.ladderOdd.raw a).sites := by
  rw [quarterTurn_offset_apply, BaseMask.mem_ladderOdd_raw_iff]
  obtain ⟨x, y⟩ := u
  simp only [NativeT, BaseMask.LadderOddCorner] at hu ⊢
  omega

/-- The charge of a native point of the twos field (the source charge table at its quarter turn). -/
theorem laplacian_twos_native (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {u : Site} (hu : NativeT (2 * (k : ℤ) + 4) u.1 u.2) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) u =
      if EvenSite (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) u) then
        (if LadderOddEvenBlack (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) u)
          then -1 else 0)
      else
        (if LadderOddOddWhite (2 * (k : ℤ) + 4) (QuarterTurn.counterclockwise.mapSite (2 * (2 * (k : ℤ) + 4), 1) u)
          then 0 else -1) := by
  rw [laplacian_twos_eq_source k hagree hperiod u]
  exact ladderOdd_laplacian_on_raw (ladderOdd_valid_twos k) hagree hperiod _
    (nativeT_rot_raw (by omega) hu)

end FLatticePaper.TwosEPolicy
