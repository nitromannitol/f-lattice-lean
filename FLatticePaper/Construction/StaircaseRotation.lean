import FLatticePaper.Construction.QuarterTurnCorrection
import FLatticePaper.Construction.StaircaseRank
import FLatticePaper.Plane.RecurrenceRotation

namespace FLatticePaper.Construction

open Farey

/-- The source pullback and harmonic correction in the occupied lower-left
chart of the near-one staircase. -/
def rotateStaircaseField (den : ℤ) (field : Field) : Field := fun point =>
  field (QuarterTurn.counterclockwise.mapSite (den, 0) point) + centeredQuarterTurnCorrection point

/-- The same duality formula in the raw B2 and B4 coordinates. -/
def rawRotateStaircaseField (den : ℤ) (field : Field) : Field := fun point =>
  field (den + 1 - point.2, point.1) + (chooseTwo point.1 - (point.1 - point.2) ^ 2 / 4)

private theorem rotateStaircase_pullback (den : ℤ) (point : Site) :
    QuarterTurn.counterclockwise.mapSite (den, 0) point = (den - point.2, point.1) := by
  apply Prod.ext <;> dsimp [QuarterTurn.mapSite, QuarterTurn.turn] <;> omega

/-- The two physical quarter-turn charts differ by the reciprocal kernel.
The reciprocal field has zero height increment along that kernel. -/
theorem rotateStaircaseField_earlierChain {den : ℤ} (hodd : den % 2 = 1) {field : Field} {constantV : ℤ}
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field 0 constantV) (point : Site) :
    rotateStaircaseField den field point =
      field (QuarterTurn.counterclockwise.mapSite (0, -1) point) + centeredQuarterTurnCorrection point := by
  have hmap : QuarterTurn.counterclockwise.mapSite (den, 0) point =
      QuarterTurn.counterclockwise.mapSite (0, -1) point + (reciprocalEvenDeck den).kernel := by
    rw [reciprocalEvenDeck_eq hodd]
    apply Prod.ext <;> dsimp [QuarterTurn.mapSite, QuarterTurn.turn] <;> ring
  change field (QuarterTurn.counterclockwise.mapSite (den, 0) point) + centeredQuarterTurnCorrection point = _
  rw [hmap]
  have h := hperiod.1 (QuarterTurn.counterclockwise.mapSite (0, -1) point)
  change field (QuarterTurn.counterclockwise.mapSite (0, -1) point + (reciprocalEvenDeck den).kernel) = _ at h
  rw [h, add_zero]

theorem rawRotateStaircaseField_chart (den : ℤ) (field : Field) :
    (fun point : Site => rawRotateStaircaseField den field (point + (0, 1))) = rotateStaircaseField den field := by
  funext point
  rw [rotateStaircaseField, rotateStaircase_pullback]
  simp only [rawRotateStaircaseField, centeredQuarterTurnCorrection, Prod.fst_add, Prod.snd_add, add_zero]
  rw [show den + 1 - (point.2 + 1) = den - point.2 by omega,
    show point.1 - (point.2 + 1) = point.1 - point.2 - 1 by omega]

theorem rotateStaircaseField_recurrent {den : ℤ} (hodd : den % 2 = 1) {field : Field}
    (hrec : Recurrent field) (hsuper : Superharmonic field) :
    Superharmonic (rotateStaircaseField den field) ∧ Recurrent (rotateStaircaseField den field) :=
  hrec.quarterTurn hsuper .counterclockwise (den, 0) (by
    change (den + 0) % 2 ≠ 0
    omega) harmonic_centeredQuarterTurnCorrection

private theorem correction_at_nearOne_kernel (den : ℤ) :
    centeredQuarterTurnCorrection (den + 1, den - 1) = chooseTwo (den + 1) := by
  change chooseTwo (den + 1) - ((den + 1) - (den - 1) - 1) ^ 2 / 4 = _
  rw [show (den + 1) - (den - 1) - 1 = 1 by omega, show (1 : ℤ) ^ 2 / 4 = 0 by decide, sub_zero]

/-- The near-one kernel pulls back to the reciprocal transverse generator,
and its transverse generator pulls back to minus the reciprocal kernel. -/
theorem rotateStaircaseField_periods {den : ℤ} (hodd : den % 2 = 1)
    {field : Field} {constantU constantV : ℤ}
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field constantU constantV) :
    HasGeneratorPeriods (Fraction.mk 1 den).rotate (rotateStaircaseField den field)
      (den + constantV + chooseTwo (den + 1)) (centeredQuarterTurnCorrection (-1, den) - constantU) := by
  constructor
  · intro point
    rw [nearOneDeck_eq hodd]
    simp only [rotateStaircaseField, rotateStaircase_pullback]
    have hpull : (den - (point + (den + 1, den - 1)).2, (point + (den + 1, den - 1)).1) =
        (den - point.2, point.1) + ((reciprocalEvenDeck den).transverse) := by
      rw [reciprocalEvenDeck_eq hodd]
      apply Prod.ext <;> dsimp <;> omega
    have hsrc := hperiod.2 (den - point.2, point.1)
    change field ((den - point.2, point.1) + (reciprocalEvenDeck den).transverse) = _ at hsrc
    rw [hpull, hsrc]
    have heven : EvenSite (den + 1, den - 1) := by change (den + 1 + (den - 1)) % 2 = 0; omega
    have hc := centeredQuarterTurnCorrection_add point heven
    change centeredQuarterTurnCorrection (point + (den + 1, den - 1)) =
      centeredQuarterTurnCorrection point + centeredQuarterTurnCorrection (den + 1, den - 1) +
        ((den + 1 + (den - 1)) / 2) * point.1 + ((den + 1 - (den - 1)) / 2) * point.2 at hc
    rw [hc, correction_at_nearOne_kernel,
      show (den + 1 + (den - 1)) / 2 = den by omega,
      show (den + 1 - (den - 1)) / 2 = 1 by omega]
    simp only [Fraction.transverseGrade, one_mul]
    omega
  · intro point
    rw [nearOneDeck_eq hodd]
    simp only [rotateStaircaseField, rotateStaircase_pullback]
    let pulled : Site := (den - (point + (-1, den)).2, (point + (-1, den)).1)
    have hshift : pulled + (reciprocalEvenDeck den).kernel = (den - point.2, point.1) := by
      rw [reciprocalEvenDeck_eq hodd]
      apply Prod.ext <;> dsimp [pulled] <;> omega
    have hpull := hperiod.1 pulled
    change field (pulled + (reciprocalEvenDeck den).kernel) = _ at hpull
    rw [hshift] at hpull
    change field pulled + centeredQuarterTurnCorrection (point + (-1, den)) = _
    have heven : EvenSite (-1, den) := by change (-1 + den) % 2 = 0; omega
    have hc := centeredQuarterTurnCorrection_add point heven
    change centeredQuarterTurnCorrection (point + (-1, den)) = centeredQuarterTurnCorrection point +
      centeredQuarterTurnCorrection (-1, den) + ((-1 + den) / 2) * point.1 + ((-1 - den) / 2) * point.2 at hc
    have holdEven : (Fraction.mk 1 den).Even := by change (1 + den) % 2 = 0; omega
    rw [hc, Fraction.rotate_of_even holdEven]
    have hsum : (-1 + den) / 2 = (den - 1) / 2 := by omega
    have hdiff : (-1 - den) / 2 = -((den + 1) / 2) := by omega
    rw [hsum, hdiff]
    simp only [Fraction.transverseGrade, neg_mul]
    omega

theorem staircase_rotate_inUnitInterval {den : ℤ} (hden : 3 ≤ den) (hodd : den % 2 = 1) :
    (Fraction.mk 1 den).rotate.InUnitInterval := by
  have heven : (Fraction.mk 1 den).Even := by change (1 + den) % 2 = 0; omega
  rw [Fraction.rotate_of_even heven]
  exact ⟨by dsimp; omega, by dsimp; omega, by dsimp; omega⟩

/-- The B2 transverse constant in the constructor's final physical chart. -/
def stairOddConstantV (den : ℤ) : ℤ := 1 - (den + 2) ^ 2 / 4

theorem centeredQuarterTurnCorrection_nearOne_transverse (den : ℤ) :
    centeredQuarterTurnCorrection (-1, den) = stairOddConstantV den := by
  change chooseTwo (-1) - (-1 - den - 1) ^ 2 / 4 = 1 - (den + 2) ^ 2 / 4
  rw [show (-1 - den - 1) ^ 2 = (den + 2) ^ 2 by ring]
  rfl

/-- The raw B2 height identity after the prescribed final centering. -/
theorem BaseMask.stairOdd_agrees_rotateStaircaseField {den : ℤ} (hden : BaseMask.stairOdd.Valid den)
    {field : Field} (hagree : (BaseMask.stairEven.raw den).Agrees field 0) :
    ((BaseMask.stairOdd.tile den hden).llCenter (BaseMask.stairOdd.tile_nonempty den hden)).Agrees
      (rotateStaircaseField den field) 0 := by
  have hformula : (BaseMask.stairOdd.raw den).Agrees (rawRotateStaircaseField den field) 0 := by
    intro point
    let pulled : (BaseMask.stairEven.raw den).sites :=
      ⟨(den + 1 - point.val.2, point.val.1), (BaseMask.mem_stairOdd_raw_pullback_iff _).mp point.property⟩
    have hpull := hagree pulled
    rw [BaseMask.stairEven_raw_height, add_zero] at hpull
    change BaseMask.stairEvenValue den (den + 1 - point.val.2, point.val.1) =
      field (den + 1 - point.val.2, point.val.1) at hpull
    rw [BaseMask.stairOdd_raw_height]
    change _ = rawRotateStaircaseField den field point.val + 0
    simp only [rawRotateStaircaseField, add_zero, hpull, chooseTwo]
  have hcenter := BaseMask.stairOdd_llCenter_agrees hden hformula
  rwa [rawRotateStaircaseField_chart] at hcenter

/-- The exact centered B2 tile is the restriction of a recurrent field at
the reduced near-one slope, with its source period and growth data. -/
theorem stairOdd_exists_recurrent_extension {den : ℤ} (hden : BaseMask.stairOdd.Valid den) :
    ∃ field : Field,
      ((BaseMask.stairOdd.tile den hden).llCenter (BaseMask.stairOdd.tile_nonempty den hden)).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den).rotate field 0 (stairOddConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).rotate.matrix ∧ Superharmonic field ∧ Recurrent field := by
  obtain ⟨field, hagree, hperiod, _, hsuper, hrec⟩ := stairEven_exists_recurrent_extension hden
  have hperiod' := rotateStaircaseField_periods hden.2 hperiod
  rw [show den + stairEvenConstantV den + chooseTwo (den + 1) = 0 by
    unfold stairEvenConstantV; omega, centeredQuarterTurnCorrection_nearOne_transverse, sub_zero] at hperiod'
  obtain ⟨hsuper', hrec'⟩ := rotateStaircaseField_recurrent hden.2 hrec hsuper
  exact ⟨rotateStaircaseField den field, BaseMask.stairOdd_agrees_rotateStaircaseField hden hagree, hperiod',
    generator_periods_growth (staircase_rotate_inUnitInterval hden.1 hden.2) hperiod', hsuper', hrec'⟩

theorem evaluateNative_empty_odd_standard_recurrent :
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative [] = .ok registers ∧ registers.standard.currentOdd.val.Agrees field 0 ∧
      HasGeneratorPeriods ((parentsAt []).current .odd) field 0 (stairOddConstantV 3) ∧
      HasQuadraticGrowth field ((parentsAt []).current .odd).matrix ∧
      Superharmonic field ∧ Recurrent field := by
  have hvalid : BaseMask.stairOdd.Valid 3 := by simp [BaseMask.Valid]
  obtain ⟨field, hagree, hperiod, hgrowth, hsuper, hrec⟩ := stairOdd_exists_recurrent_extension hvalid
  exact ⟨BaseRun.empty.registers.llCenter, field, evaluateNative_base .empty,
    hagree, hperiod, hgrowth, hsuper, hrec⟩

theorem evaluateNative_twos_odd_standard_recurrent (extra : ℕ) :
    let word := (BaseRun.twos extra).word
    let fraction := (parentsAt word).current .odd
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧ registers.standard.currentOdd.val.Agrees field 0 ∧
      HasGeneratorPeriods fraction field 0 (stairOddConstantV (2 * (extra : ℤ) + 3 + 2)) ∧
      HasQuadraticGrowth field fraction.matrix ∧ Superharmonic field ∧ Recurrent field := by
  dsimp only
  rw [twos_current_odd]
  have hvalid : BaseMask.stairOdd.Valid (2 * (extra : ℤ) + 3 + 2) := by
    change 3 ≤ 2 * (extra : ℤ) + 3 + 2 ∧ (2 * (extra : ℤ) + 3 + 2) % 2 = 1
    omega
  obtain ⟨field, hagree, hperiod, hgrowth, hsuper, hrec⟩ := stairOdd_exists_recurrent_extension hvalid
  exact ⟨(BaseRun.twos extra).registers.llCenter, field, evaluateNative_base _,
    hagree, hperiod, hgrowth, hsuper, hrec⟩

end FLatticePaper.Construction
