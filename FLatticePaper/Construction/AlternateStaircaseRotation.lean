import FLatticePaper.Construction.AlternateStaircaseExtension
import FLatticePaper.Construction.StaircaseRotation
import FLatticePaper.Plane.AlternatePeriods

namespace FLatticePaper.Construction

open Farey

theorem BaseMask.stairOddAlt_agrees_rotateStaircaseField {den : ℤ} (hden : BaseMask.stairOddAlt.Valid den)
    {field : Field} (hagree : (BaseMask.stairEvenAlt.raw den).Agrees field 0) :
    ((BaseMask.stairOddAlt.tile den hden).llCenter (BaseMask.stairOddAlt.tile_nonempty den hden)).Agrees
      (rotateStaircaseField den field) 0 := by
  have hformula : (BaseMask.stairOddAlt.raw den).Agrees (rawRotateStaircaseField den field) 0 := by
    intro point
    let pulled : (BaseMask.stairEvenAlt.raw den).sites :=
      ⟨(den + 1 - point.val.2, point.val.1),
        (BaseMask.mem_stairOddAlt_raw_pullback_iff hden.1 _).mp point.property⟩
    have hpull := hagree pulled
    rw [BaseMask.stairEvenAlt_raw_height, add_zero] at hpull
    change BaseMask.stairEvenAltBackground den (den + 1 - point.val.2, point.val.1) +
      (if BaseMask.StairEvenAltBump den (den + 1 - point.val.2, point.val.1) then 1 else 0) =
        field (den + 1 - point.val.2, point.val.1) at hpull
    rw [BaseMask.stairOddAlt_raw_height]
    change _ = rawRotateStaircaseField den field point.val + 0
    simp only [rawRotateStaircaseField, hpull, add_zero, chooseTwo]
  have hcenter := BaseMask.stairOddAlt_llCenter_agrees hden hformula
  rwa [rawRotateStaircaseField_chart] at hcenter

theorem stairOddAlt_exists_extension {den : ℤ} (hden : BaseMask.stairOddAlt.Valid den) :
    ∃ field : Field,
      ((BaseMask.stairOddAlt.tile den hden).llCenter (BaseMask.stairOddAlt.tile_nonempty den hden)).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den).rotate field (-1) (stairOddConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).rotate.matrix := by
  obtain ⟨field, hagree, hperiod, _⟩ := stairEvenAlt_exists_extension hden
  have hrot := rotateStaircaseField_periods hden.2 hperiod
  rw [show den + (stairEvenConstantV den - 1) + chooseTwo (den + 1) = -1 by
    unfold stairEvenConstantV; omega, centeredQuarterTurnCorrection_nearOne_transverse, sub_zero] at hrot
  exact ⟨rotateStaircaseField den field, BaseMask.stairOddAlt_agrees_rotateStaircaseField hden hagree,
    hrot, generator_periods_growth (staircase_rotate_inUnitInterval hden.1 hden.2) hrot⟩

theorem evaluateNative_empty_odd_alternate_extension :
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative [] = .ok registers ∧ registers.alternate.currentOdd.val.Agrees field 0 ∧
      HasGeneratorPeriods ((parentsAt []).current .odd) field (-1) (stairOddConstantV 3) ∧
      HasQuadraticGrowth field ((parentsAt []).current .odd).matrix := by
  have hvalid : BaseMask.stairOddAlt.Valid 3 := by simp [BaseMask.Valid]
  obtain ⟨field, hagree, hperiod, hgrowth⟩ := stairOddAlt_exists_extension hvalid
  exact ⟨BaseRun.empty.registers.llCenter, field, evaluateNative_base .empty, hagree, hperiod, hgrowth⟩

theorem evaluateNative_twos_odd_alternate_extension (extra : ℕ) :
    let word := (BaseRun.twos extra).word
    let fraction := (parentsAt word).current .odd
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧ registers.alternate.currentOdd.val.Agrees field 0 ∧
      HasGeneratorPeriods fraction field (-1) (stairOddConstantV (2 * (extra : ℤ) + 3 + 2)) ∧
      HasQuadraticGrowth field fraction.matrix := by
  dsimp only
  rw [twos_current_odd]
  have hvalid : BaseMask.stairOddAlt.Valid (2 * (extra : ℤ) + 3 + 2) := by
    change 3 ≤ 2 * (extra : ℤ) + 3 + 2 ∧ (2 * (extra : ℤ) + 3 + 2) % 2 = 1
    omega
  obtain ⟨field, hagree, hperiod, hgrowth⟩ := stairOddAlt_exists_extension hvalid
  exact ⟨(BaseRun.twos extra).registers.llCenter, field, evaluateNative_base _, hagree, hperiod, hgrowth⟩

private theorem not_integerAffine_of_odd_increment {field : Field} (period : Site)
    (hcol : period.1 % 2 = 0) (hrow : period.2 % 2 = 0)
    (hodd : (field period - field 0) % 2 = 1) : ¬ IntegerAffine field := by
  rintro ⟨gradient, constant, haffine⟩
  have hcol' : period.1 = 2 * (period.1 / 2) := by omega
  have hrow' : period.2 = 2 * (period.2 / 2) := by omega
  have heq : field period - field 0 =
      2 * (gradient.1 * (period.1 / 2) + gradient.2 * (period.2 / 2)) := by
    rw [haffine period, haffine 0]
    simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, zero_add]
    linear_combination gradient.1 * hcol' + gradient.2 * hrow'
  rw [heq] at hodd
  omega

/-- B3 and B1 have different transverse constants in their common raw chart. -/
theorem stairEvenAltField_sub_standard_not_integerAffine {den : ℤ} (hodd : den % 2 = 1)
    {standard : Field} {constantU constantV : ℤ}
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) standard constantU constantV) :
    ¬ IntegerAffine (fun site => stairEvenAltField den standard site - standard site) := by
  have halt := stairEvenAltField_periods hperiod
  have hstd0 := hperiod.2 (0 : Site)
  have halt0 := halt.2 (0 : Site)
  change standard (0 + (reciprocalEvenDeck den).transverse) = _ at hstd0
  change stairEvenAltField den standard (0 + (reciprocalEvenDeck den).transverse) = _ at halt0
  rw [reciprocalEvenDeck_eq hodd] at hstd0 halt0
  simp only [zero_add, Fraction.transverseGrade, Prod.fst_zero, Prod.snd_zero, mul_zero, sub_zero] at hstd0 halt0
  apply not_integerAffine_of_odd_increment (1 - den, 1 + den)
  · change (1 - den) % 2 = 0
    omega
  · change (1 + den) % 2 = 0
    omega
  · rw [hstd0, halt0]
    omega

/-- B4 and B2 differ by an odd increment on the doubled near-one kernel. -/
theorem stairOddAlt_sub_standard_not_integerAffine {den : ℤ} (hodd : den % 2 = 1)
    {standard alternate : Field}
    (hstandard : HasGeneratorPeriods (Fraction.mk 1 den).rotate standard 0 (stairOddConstantV den))
    (halternate : HasGeneratorPeriods (Fraction.mk 1 den).rotate alternate (-1) (stairOddConstantV den)) :
    ¬ IntegerAffine (fun site => alternate site - standard site) := by
  have hstd0 := hstandard.1 (0 : Site)
  have halt0 := halternate.1 (0 : Site)
  rw [nearOneDeck_eq hodd, zero_add, add_zero] at hstd0
  rw [nearOneDeck_eq hodd, zero_add] at halt0
  apply not_integerAffine_of_odd_increment (den + 1, den - 1)
  · change (den + 1) % 2 = 0
    omega
  · change (den - 1) % 2 = 0
    omega
  · rw [hstd0, halt0]
    omega

end FLatticePaper.Construction
