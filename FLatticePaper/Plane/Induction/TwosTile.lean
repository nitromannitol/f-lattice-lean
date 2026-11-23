import FLatticePaper.Plane.Induction.TwosBaseIdentity
import FLatticePaper.Plane.Induction.TwosPeriods
import FLatticePaper.Construction.AlternateLadderExtension
import FLatticePaper.Construction.LadderExtension

/-! Task 36 (hbaseTwoId), step 2: the tile identity on the alternate tile. The twos midpoint `twoH` agrees with the
explicit ladder alternate `ladderOddAltValue` on every site of the alternate tile, by explicit reductions of the odd field
at the two shifted points. -/

namespace FLatticePaper.Induction.TwosTile

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Induction.TwosBaseIdentity

theorem combine_even (d : ℤ) (hd : d % 2 = 0) (i j : ℤ) :
    (Fraction.mk 1 d).modifiedDeck.combine i j = (2 * d * i + (1 - d) * j, 2 * i + (1 + d) * j) := by
  have hk := kernel_even d hd
  have ht := transverse_eq d
  simp only [PeriodDeck.combine, hk, ht]
  ext <;> simp <;> ring

theorem period_den_eq (d : ℤ) : (Fraction.mk 1 d).periodDenominator = d ^ 2 + 2 * d - 1 := by
  simp [Fraction.periodDenominator]

/-- The odd field reduced at a deck translate of a point. -/
theorem S0_red {d : ℤ} {S0 : Site → ℤ} {cV0 : ℤ} (hS0 : HasGeneratorPeriods (Fraction.mk 1 d) S0 0 cV0)
    (q : Site) (i j : ℤ) :
    S0 (q + (Fraction.mk 1 d).modifiedDeck.combine i j) =
      S0 q + j * (cV0 - (d * q.2 - q.1)) - (d ^ 2 + 2 * d - 1) * chooseTwo j := by
  rw [periods_combine hS0 q i j]
  unfold periodIncrement
  rw [transverseGrade_eq, period_den_eq]
  ring

theorem S_alt_eq {d : ℤ} {S : Site → ℤ}
    (hS : (BaseMask.ladderOddAlt.raw d).Agrees S 0) (w : Site)
    (hw : w ∈ (BaseMask.ladderOddAlt.raw d).sites) :
    S w = BaseMask.ladderOddAltValue d w := by
  have h := hS ⟨w, hw⟩
  rw [BaseMask.ladderOddAlt_raw_height] at h
  simpa using h.symm

theorem S0_eq {d : ℤ} {S : Site → ℤ}
    (hS : (BaseMask.ladderOdd.raw d).Agrees S 0) (q : Site)
    (hq : q ∈ (BaseMask.ladderOdd.raw d).sites) :
    S q = BaseMask.ladderOddValue d q := by
  have h := hS ⟨q, hq⟩
  rw [BaseMask.ladderOdd_raw_height] at h
  simpa using h.symm

/-- Twice the odd tile value, without division. -/
theorem two_mul_ladderOddValue (d : ℤ) (p : Site) :
    2 * BaseMask.ladderOddValue d p =
      -(p.2 * (p.2 - 1)) + 2 * min 0 (p.1 - 1) + 2 * max (p.2 + p.1 - d - 2) 0 + 2 * min (d + 1 - p.1) 0 +
        2 * (if BaseMask.LadderOddBump d p then 1 else 0) := by
  have h2 : (2 : ℤ) ∣ p.2 * (p.2 - 1) := (Int.even_mul_pred_self p.2).two_dvd
  have hdiv := Int.mul_ediv_cancel' h2
  unfold BaseMask.ladderOddValue
  linarith

/-- Twice the alternate tile value, without division. -/
theorem two_mul_ladderOddAltValue (d : ℤ) (p : Site) :
    2 * BaseMask.ladderOddAltValue d p =
      -(p.2 * (p.2 + 1)) + 2 * min p.1 0 + 2 * max (p.1 + p.2 - d) 0 + 2 * min (d - p.1 - 1) 0 +
        2 * (if BaseMask.LadderOddAltCorner d p ∨ BaseMask.LadderOddAltDiagonal d p then 1 else 0) := by
  have h2 : (2 : ℤ) ∣ p.2 * (p.2 + 1) := (Int.even_mul_succ_self p.2).two_dvd
  have hdiv := Int.mul_ediv_cancel' h2
  unfold BaseMask.ladderOddAltValue
  linarith

theorem two_mul_dcorr_half (d : ℤ) : 2 * (d * (d + 1) / 2) = d ^ 2 + d := by
  have h2 : (2 : ℤ) ∣ d * (d + 1) := (Int.even_mul_succ_self d).two_dvd
  have hdiv := Int.mul_ediv_cancel' h2
  linarith

end FLatticePaper.Induction.TwosTile
