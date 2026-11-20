import FLatticePaper.Construction.LadderExtension
import FLatticePaper.Construction.QuarterTurnCorrection
import FLatticePaper.Plane.RecurrenceRotation

namespace FLatticePaper.Construction

open Farey

/-- The B5-to-B6 harmonic rotation in the centered physical chart. -/
def rotateLadderField (den : ℤ) (field : Field) : Field := fun point =>
  field (QuarterTurn.counterclockwise.mapSite (2 * den, 1) point) + centeredQuarterTurnCorrection point

private theorem rotateLadder_pullback (den : ℤ) (point : Site) :
    QuarterTurn.counterclockwise.mapSite (2 * den, 1) point = (2 * den - point.2, point.1 + 1) := by
  apply Prod.ext
  · change -point.2 + 2 * den = 2 * den - point.2
    omega
  · rfl

theorem rotateLadderField_recurrent {den : ℤ} {field : Field}
    (hrec : Recurrent field) (hsuper : Superharmonic field) :
    Superharmonic (rotateLadderField den field) ∧ Recurrent (rotateLadderField den field) :=
  hrec.quarterTurn hsuper .counterclockwise (2 * den, 1) (by
    change (2 * den + 1) % 2 ≠ 0
    omega) harmonic_centeredQuarterTurnCorrection

private theorem correction_at_ladder_kernel (den : ℤ) :
    centeredQuarterTurnCorrection (den + 1, den - 1) = chooseTwo (den + 1) := by
  change chooseTwo (den + 1) - ((den + 1) - (den - 1) - 1) ^ 2 / 4 = _
  rw [show (den + 1) - (den - 1) - 1 = 1 by omega, show (1 : ℤ) ^ 2 / 4 = 0 by decide, sub_zero]

/-- The B6 transverse constant in the constructor's physical chart. -/
def ladderEvenConstantV (den : ℤ) : ℤ := centeredQuarterTurnCorrection (-2, 2 * den)

theorem ladderEvenConstantV_eq (den : ℤ) : ladderEvenConstantV den = 1 - den ^ 2 - 3 * den := by
  have h := four_mul_centeredQuarterTurnCorrection (-2, 2 * den)
  change 4 * ladderEvenConstantV den =
    (-2) ^ 2 + 2 * (-2) * (2 * den) - (2 * den) ^ 2 - 2 * (2 * den) -
      ((-2) + 2 * den) % 2 at h
  rw [show ((-2 : ℤ) + 2 * den) % 2 = 0 by omega] at h
  linarith

theorem hasGeneratorPeriods_rotateLadderField {den : ℤ} (heven : den % 2 = 0) {field : Field}
    {constantU constantV : ℤ} (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field constantU constantV) :
    HasGeneratorPeriods (Fraction.mk 1 den).rotate (rotateLadderField den field)
      (den + constantV + chooseTwo (den + 1)) (ladderEvenConstantV den - constantU) := by
  constructor
  · intro point
    rw [nearOneLadderDeck_eq heven]
    simp only [rotateLadderField, rotateLadder_pullback]
    have hsource : (2 * den - (point + (den + 1, den - 1)).2, (point + (den + 1, den - 1)).1 + 1) =
        (2 * den - point.2, point.1 + 1) + (reciprocalLadderDeck den).transverse := by
      rw [reciprocalLadderDeck_eq heven]
      apply Prod.ext <;> dsimp <;> omega
    have hshift := hperiod.2 (2 * den - point.2, point.1 + 1)
    change field ((2 * den - point.2, point.1 + 1) + (reciprocalLadderDeck den).transverse) = _ at hshift
    rw [hsource, hshift]
    have hphase : EvenSite (den + 1, den - 1) := by change (den + 1 + (den - 1)) % 2 = 0; omega
    have hc := centeredQuarterTurnCorrection_add point hphase
    change centeredQuarterTurnCorrection (point + (den + 1, den - 1)) =
      centeredQuarterTurnCorrection point + centeredQuarterTurnCorrection (den + 1, den - 1) +
        ((den + 1 + (den - 1)) / 2) * point.1 + ((den + 1 - (den - 1)) / 2) * point.2 at hc
    rw [hc, correction_at_ladder_kernel,
      show (den + 1 + (den - 1)) / 2 = den by omega,
      show (den + 1 - (den - 1)) / 2 = 1 by omega]
    simp only [Fraction.transverseGrade, one_mul]
    ring
  · intro point
    rw [nearOneLadderDeck_eq heven]
    simp only [rotateLadderField, rotateLadder_pullback]
    let pulled : Site := (2 * den - (point + (-2, 2 * den)).2, (point + (-2, 2 * den)).1 + 1)
    have hsource : pulled + (reciprocalLadderDeck den).kernel = (2 * den - point.2, point.1 + 1) := by
      rw [reciprocalLadderDeck_eq heven]
      apply Prod.ext <;> dsimp [pulled] <;> omega
    have hshift := hperiod.1 pulled
    change field (pulled + (reciprocalLadderDeck den).kernel) = field pulled + constantU at hshift
    rw [hsource] at hshift
    change field pulled + centeredQuarterTurnCorrection (point + (-2, 2 * den)) = _
    have hphase : EvenSite (-2, 2 * den) := by change (-2 + 2 * den) % 2 = 0; omega
    have hc := centeredQuarterTurnCorrection_add point hphase
    change centeredQuarterTurnCorrection (point + (-2, 2 * den)) = centeredQuarterTurnCorrection point +
      centeredQuarterTurnCorrection (-2, 2 * den) + ((-2 + 2 * den) / 2) * point.1 +
      ((-2 - 2 * den) / 2) * point.2 at hc
    have holdOdd : (Fraction.mk 1 den).Odd := by change (1 + den) % 2 = 1; omega
    rw [hshift, hc, Fraction.rotate_of_odd holdOdd,
      show (-2 + 2 * den) / 2 = den - 1 by omega,
      show (-2 - 2 * den) / 2 = -(den + 1) by omega]
    simp only [Fraction.transverseGrade, ladderEvenConstantV]
    ring

theorem rotateLadderField_periods {den : ℤ} (heven : den % 2 = 0) {field : Field}
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 (stairEvenConstantV den)) :
    HasGeneratorPeriods (Fraction.mk 1 den).rotate (rotateLadderField den field) 0 (ladderEvenConstantV den) := by
  have h := hasGeneratorPeriods_rotateLadderField heven hperiod
  rw [show den + stairEvenConstantV den + chooseTwo (den + 1) = 0 by unfold stairEvenConstantV; omega,
    sub_zero] at h
  exact h

theorem BaseMask.ladderEven_agrees_rotateLadderField {den : ℤ} (hden : BaseMask.ladderEven.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOdd.raw den).Agrees field 0) :
    ((BaseMask.ladderEven.tile den hden).llCenter (BaseMask.ladderEven.tile_nonempty den hden)).Agrees
      (rotateLadderField den field) 0 := by
  let raw : Field := fun point =>
    field (2 * den + 1 - point.2, point.1 + 1) + (chooseTwo point.1 - (point.1 - point.2) ^ 2 / 4)
  have hraw : (BaseMask.ladderEven.raw den).Agrees raw 0 := by
    intro point
    let pulled : (BaseMask.ladderOdd.raw den).sites := ⟨(2 * den + 1 - point.val.2, point.val.1 + 1),
      (BaseMask.mem_ladderEven_raw_pullback_iff point.val).mp point.property⟩
    have hpull := hagree pulled
    rw [BaseMask.ladderOdd_raw_height, add_zero] at hpull
    change BaseMask.ladderOddValue den (2 * den + 1 - point.val.2, point.val.1 + 1) =
      field (2 * den + 1 - point.val.2, point.val.1 + 1) at hpull
    rw [BaseMask.ladderEven_raw_height]
    change _ = raw point.val + 0
    simp only [raw, hpull, chooseTwo, add_zero]
  have hcenter := BaseMask.ladderEven_llCenter_agrees hden hraw
  have hchart : (fun point : Site => raw (point + (0, 1))) = rotateLadderField den field := by
    funext point
    rw [rotateLadderField, rotateLadder_pullback]
    simp only [raw, centeredQuarterTurnCorrection, Prod.fst_add, Prod.snd_add, add_zero]
    rw [show 2 * den + 1 - (point.2 + 1) = 2 * den - point.2 by omega,
      show point.1 - (point.2 + 1) = point.1 - point.2 - 1 by omega]
  rwa [hchart] at hcenter

theorem ladder_rotate_inUnitInterval {den : ℤ} (hden : 4 ≤ den) (heven : den % 2 = 0) :
    (Fraction.mk 1 den).rotate.InUnitInterval := by
  have hodd : (Fraction.mk 1 den).Odd := by change (1 + den) % 2 = 1; omega
  rw [Fraction.rotate_of_odd hodd]
  exact ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega⟩

/-- The literal near-one B6 field of the prescribed periods and quadratic growth. -/
theorem ladderEven_exists_extension {den : ℤ} (hden : BaseMask.ladderEven.Valid den) :
    ∃ field : Field,
      ((BaseMask.ladderEven.tile den hden).llCenter (BaseMask.ladderEven.tile_nonempty den hden)).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den).rotate field 0 (ladderEvenConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).rotate.matrix := by
  obtain ⟨source, hagree, hperiod, _⟩ := ladderOdd_exists_extension hden
  have hrot := rotateLadderField_periods hden.2 hperiod
  exact ⟨rotateLadderField den source, BaseMask.ladderEven_agrees_rotateLadderField hden hagree,
    hrot, generator_periods_growth (ladder_rotate_inUnitInterval hden.1 hden.2) hrot⟩

theorem evaluateNative_twos_even_standard_extension (extra : ℕ) :
    let word := (BaseRun.twos extra).word
    let den : ℤ := 2 * (extra : ℤ) + 3 + 1
    let fraction := (parentsAt word).current .even
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧ registers.standard.currentEven.val.Agrees field 0 ∧
      HasGeneratorPeriods fraction field 0 (ladderEvenConstantV den) ∧
      HasQuadraticGrowth field fraction.matrix := by
  dsimp only
  rw [twos_current_even]
  have hvalid : BaseMask.ladderEven.Valid (2 * (extra : ℤ) + 3 + 1) := by
    change 4 ≤ 2 * (extra : ℤ) + 3 + 1 ∧ (2 * (extra : ℤ) + 3 + 1) % 2 = 0
    omega
  obtain ⟨field, hagree, hperiod, hgrowth⟩ := ladderEven_exists_extension hvalid
  exact ⟨(BaseRun.twos extra).registers.llCenter, field, evaluateNative_base _, hagree, hperiod, hgrowth⟩

end FLatticePaper.Construction
