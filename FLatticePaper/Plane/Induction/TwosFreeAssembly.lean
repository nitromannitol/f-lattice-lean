import FLatticePaper.Plane.Induction.TwosFreeCases
import FLatticePaper.Plane.Induction.TwosFreeDrop
import FLatticePaper.Plane.Induction.TwosWhiteSel

/-! Twos flatness, the free centres (sign `+1`): every free tile centre is white (charge `0`), its selected input is its free
displacement (`twosSel_free_self`), and the destination's rank drops by one on a flat edge. -/

noncomputable section

namespace FLatticePaper.TwosEPolicy

open FLatticePaper FLatticePaper.Construction FLatticePaper.Induction Farey
open scoped Classical

/-- A native even site in an explicit white piece has charge `0`. -/
theorem lap_even_white (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hpar : (x + y) % 2 = 0)
    (hEW : EvenWhitePiece (2 * (k : ℤ) + 4) x y) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = 0 := by
  rw [laplacian_twos_native k hagree hperiod hn]
  simp only [rot_twos_ccw]
  have he : ¬ EvenSite (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
    unfold EvenSite
    dsimp only
    omega
  rw [if_neg he]
  have hL : LadderOddOddWhite (2 * (k : ℤ) + 4) (2 * (2 * (k : ℤ) + 4) - y, x + 1) := by
    by_contra hc
    exact (even_black_explicit (2 * (k : ℤ) + 4) x y).mp hc hEW
  rw [if_pos hL]

/-- The charge at a free odd native site is `0`. -/
theorem lap_odd_free (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hpar : (x + y) % 2 = 1) (hF : FreeSite (2 * (k : ℤ) + 4) x y) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = 0 := by
  apply lap_odd_value k hagree hperiod hn hpar
  intro h
  rw [odd_black_explicit] at h
  unfold FreeSite FreeHSite FreeVSite at hF
  omega

/-- Every free native tile centre is white: its charge is `0`. -/
theorem lap_free_zero (k : ℕ) {S : Field}
    (hagree : (BaseMask.ladderOdd.raw (2 * (k : ℤ) + 4)).Agrees S 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 (2 * (k : ℤ) + 4)) S 0 (stairEvenConstantV (2 * (k : ℤ) + 4)))
    {x y : ℤ} (hn : NativeT (2 * (k : ℤ) + 4) x y) (hF : FreeSite (2 * (k : ℤ) + 4) x y) :
    laplacian (standardField (List.replicate (k + 1) Digit.two)) (x, y) = 0 := by
  have ha : (4 : ℤ) ≤ 2 * (k : ℤ) + 4 := by omega
  by_cases hpar : (x + y) % 2 = 1
  · exact lap_odd_free k hagree hperiod hn hpar hF
  · have hpar0 : (x + y) % 2 = 0 := by omega
    apply lap_even_white k hagree hperiod hn hpar0
    unfold FreeSite FreeHSite FreeVSite at hF
    rcases hF with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩) | (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · exfalso
      omega
    · by_cases hxa : x = 2 * (k : ℤ) + 4
      · exact ewp_10 ⟨hxa, by omega⟩
      · exact ewp_4 ⟨by omega, by omega, by omega⟩
    · exfalso
      omega
    · exact ewp_3 ⟨h1, by omega, by omega⟩
    · exact ewp_2 ⟨h1, by omega, by omega⟩

end FLatticePaper.TwosEPolicy
