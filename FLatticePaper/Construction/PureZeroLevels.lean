import FLatticePaper.Construction.StaircaseStrips
import FLatticePaper.Construction.StaircaseRotation
import FLatticePaper.Construction.LadderRotation

namespace FLatticePaper.Construction

open Farey

private theorem eq_of_same_grade {fraction : Fraction} (hinterval : fraction.InUnitInterval) (hreduced : fraction.Reduced)
    {field : Field} {constantV : ℤ} (hperiod : HasGeneratorPeriods fraction field 0 constantV)
    {site representative : Site} (hgrade : fraction.transverseGrade site = fraction.transverseGrade representative)
    (hparity : fraction.Even ∨ (EvenSite site ∧ EvenSite representative)) : field site = field representative := by
  have hzero : fraction.transverseGrade (site - representative) = 0 := by rw [Fraction.transverseGrade_sub, hgrade, sub_self]
  obtain ⟨index, hindex⟩ := fraction.exists_kernel_multiple hreduced hzero
  have heven : EvenSite (site - representative) := by
    rcases hparity with hp | ⟨hs, hr⟩
    · rw [hindex]
      change (index * fraction.den + 0 * (fraction.num - fraction.den) +
        (index * fraction.num + 0 * (fraction.num + fraction.den))) % 2 = 0
      change (fraction.num + fraction.den) % 2 = 0 at hp
      simp only [zero_mul, add_zero]
      rw [add_comm, ← mul_add, Int.mul_emod, hp, mul_zero, Int.zero_emod]
    · change (site.1 - representative.1 + (site.2 - representative.2)) % 2 = 0
      unfold EvenSite at hs hr
      omega
  have hspan : site - representative ∈ fraction.modifiedDeck.span :=
    (fraction.mem_modifiedDeck_iff _).mpr ⟨⟨index, 0, hindex⟩, heven⟩
  obtain ⟨i, j, hcombine⟩ := hspan
  rw [hcombine, Fraction.modifiedDeck_combine, Fraction.transverseGrade_combine] at hzero
  have hj : j = 0 := (mul_eq_zero.mp hzero).resolve_left (Fraction.periodDenominator_pos hinterval).ne'
  subst j
  have hsite : representative + fraction.modifiedDeck.combine i 0 = site := by rw [← hcombine, add_comm, sub_add_cancel]
  have h := generator_period_formula hinterval hperiod representative i 0
  rw [hsite] at h
  simp at h
  exact h

private theorem reciprocal_inUnitInterval {den : ℤ} (h : 1 ≤ den) : (Fraction.mk 1 den).InUnitInterval := by
  change 0 < den ∧ 0 ≤ (1 : ℤ) ∧ 1 ≤ den
  omega

private theorem reciprocal_reduced (den : ℤ) : (Fraction.mk 1 den).Reduced :=
  ⟨1, 0, by simp⟩

/-- The added reciprocal even zero level is contained in the entire zero strip. -/
theorem stairEven_additional_zero {den : ℤ} (hden : BaseMask.stairEven.Valid den) {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den)) (site : Site)
    (hgrade : (Fraction.mk 1 den).transverseGrade site = den - 1) : field site = 0 := by
  have hlo := hden.1
  simp only [Fraction.transverseGrade, one_mul] at hgrade
  exact stairEven_eq_zero_of_transverse hden hagree hperiod site (by omega) (by omega)

/-- The genuine odd reciprocal doubled ladder vanishes on the added level
in the even physical phase. The representative uses its diagonal bonus. -/
theorem ladderOdd_additional_zero {den : ℤ} (hden : BaseMask.ladderOdd.Valid den) {field : Field}
    (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den)) (site : Site)
    (hgrade : (Fraction.mk 1 den).transverseGrade site = den) (hphase : EvenSite site) : field site = 0 := by
  have hd := hden.1
  have hpoint : (den, 2) ∈ (BaseMask.ladderOdd.raw den).sites := by
    apply BaseMask.mem_ladderOdd_raw_iff.mpr
    change (2 - den ≤ den ∧ den ≤ 2 * den) ∧ (0 ≤ (2 : ℤ) ∧ 2 ≤ den + 2) ∧ _
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, Or.inr ⟨by omega, by omega, by rintro (⟨h, -⟩ | ⟨h, -⟩) <;> omega⟩⟩
  have hbump : BaseMask.LadderOddBump den (den, 2) := Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
  have hvalue := hagree ⟨(den, 2), hpoint⟩
  rw [BaseMask.ladderOdd_raw_height, add_zero] at hvalue
  have hraw : BaseMask.ladderOddValue den (den, 2) = 0 := by
    simp only [BaseMask.ladderOddValue, if_pos hbump, show min (0 : ℤ) (den - 1) = 0 by omega,
      show 2 + den - den - 2 = 0 by omega, show min (den + 1 - den) (0 : ℤ) = 0 by omega]
    decide
  have hsame : (Fraction.mk 1 den).transverseGrade site = (Fraction.mk 1 den).transverseGrade (den, 2) := by
    rw [hgrade]
    simp [Fraction.transverseGrade]
    ring
  have hrep : EvenSite (den, 2) := by
    have hdphase := hden.2
    change (den + 2) % 2 = 0
    omega
  exact (eq_of_same_grade (reciprocal_inUnitInterval (by omega)) (reciprocal_reduced den) hperiod hsame
    (Or.inr ⟨hphase, hrep⟩)).trans (hvalue.symm.trans hraw)

/-- The odd near-one staircase has its extra zero in the even physical phase,
with the genuine one-row restoration of the vertical formula. -/
theorem rotateStaircaseField_additional_zero {den : ℤ} (hden : BaseMask.stairOdd.Valid den) {field : Field}
    (hagree : (BaseMask.stairEven.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den)) (site : Site)
    (hgrade : (Fraction.mk 1 den).rotate.transverseGrade site = den - 1) (hphase : EvenSite site) :
    rotateStaircaseField den field site = 0 := by
  have hd := hden.1
  have hraw : (1, den - 1) ∈ (BaseMask.stairEven.raw den).sites := by
    apply BaseMask.mem_stairEven_body <;> dsimp <;> omega
  have hbump : ¬ BaseMask.StairEvenCorner den (1, den - 1) := by simp [BaseMask.StairEvenCorner]
  have hv := hagree ⟨(1, den - 1), hraw⟩
  rw [BaseMask.stairEven_raw_height, add_zero] at hv
  have hrepresentative : rotateStaircaseField den field (den - 1, den - 1) = 0 := by
    have hpull : QuarterTurn.counterclockwise.mapSite (den, 0) (den - 1, den - 1) = (1, den - 1) := by
      apply Prod.ext <;> dsimp [QuarterTurn.mapSite, QuarterTurn.turn] <;> omega
    rw [rotateStaircaseField, hpull, ← hv]
    simp [BaseMask.stairEvenValue, hbump, centeredQuarterTurnCorrection, chooseTwo]
  have hrot := rotateStaircaseField_periods hden.2 hperiod
  rw [show den + stairEvenConstantV den + chooseTwo (den + 1) = 0 by unfold stairEvenConstantV; omega] at hrot
  have hinterval := reciprocal_inUnitInterval (den := den) (by omega)
  have hfrac : (Fraction.mk 1 den).rotate = ⟨(den - 1) / 2, (den + 1) / 2⟩ := by
    apply Fraction.rotate_of_even
    change (1 + den) % 2 = 0
    have := hden.2
    omega
  have hsame : (Fraction.mk 1 den).rotate.transverseGrade site =
      (Fraction.mk 1 den).rotate.transverseGrade (den - 1, den - 1) := by
    rw [hgrade, hfrac]
    have h := hden.2
    change den - 1 = (den + 1) / 2 * (den - 1) - (den - 1) / 2 * (den - 1)
    rw [← sub_mul, show (den + 1) / 2 - (den - 1) / 2 = 1 by omega, one_mul]
  have hp : EvenSite (den - 1, den - 1) := by change (den - 1 + (den - 1)) % 2 = 0; omega
  exact (eq_of_same_grade (staircase_rotate_inUnitInterval hd hden.2) (Fraction.rotate_reduced hinterval (reciprocal_reduced den))
    hrot hsame (Or.inr ⟨hphase, hp⟩)).trans hrepresentative

/-- The genuine near-one even doubled ladder vanishes on the whole added
level through its restored representative `(den - 1, den - 1)`. -/
theorem rotateLadderField_additional_zero {den : ℤ} (hden : BaseMask.ladderEven.Valid den) {field : Field}
    (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0)
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den)) (site : Site)
    (hgrade : (Fraction.mk 1 den).rotate.transverseGrade site = 2 * den - 2) :
    rotateLadderField den field site = 0 := by
  have hd := hden.1
  have hraw : (den + 1, den) ∈ (BaseMask.ladderOdd.raw den).sites := by
    apply BaseMask.mem_ladderOdd_body <;> dsimp <;> omega
  have hbump : ¬ BaseMask.LadderOddBump den (den + 1, den) := by simp only [BaseMask.LadderOddBump]; omega
  have hv := hagree ⟨(den + 1, den), hraw⟩
  rw [BaseMask.ladderOdd_raw_height, add_zero] at hv
  have hrepresentative : rotateLadderField den field (den - 1, den - 1) = 0 := by
    have hpull : QuarterTurn.counterclockwise.mapSite (2 * den, 1) (den - 1, den - 1) = (den + 1, den) := by
      apply Prod.ext <;> dsimp [QuarterTurn.mapSite, QuarterTurn.turn] <;> omega
    rw [rotateLadderField, hpull, ← hv]
    simp only [BaseMask.ladderOddValue, if_neg hbump, centeredQuarterTurnCorrection,
      min_eq_left (show (0 : ℤ) ≤ den + 1 - 1 by omega), sub_self, chooseTwo]
    rw [show den + (den + 1) - den - 2 = den - 1 by ring, max_eq_left (by omega : 0 ≤ den - 1),
      show ((0 : ℤ) - 1) ^ 2 / 4 = 0 by decide,
      show den * (den - 1) = (den - 1) * (den - 1 - 1) + (den - 1) * 2 by ring,
      Int.add_mul_ediv_right _ _ (by decide)]
    omega
  have hodd : (Fraction.mk 1 den).Odd := by change (1 + den) % 2 = 1; have := hden.2; omega
  have hinterval := reciprocal_inUnitInterval (den := den) (by omega)
  have hsame : (Fraction.mk 1 den).rotate.transverseGrade site =
      (Fraction.mk 1 den).rotate.transverseGrade (den - 1, den - 1) := by
    rw [hgrade, Fraction.rotate_of_odd hodd]
    simp [Fraction.transverseGrade]
    ring
  exact (eq_of_same_grade (ladder_rotate_inUnitInterval hd hden.2) (Fraction.rotate_reduced hinterval (reciprocal_reduced den))
    (rotateLadderField_periods hden.2 hperiod) hsame (Or.inl (Fraction.rotate_even_of_odd hodd))).trans hrepresentative

end FLatticePaper.Construction
