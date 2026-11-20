import FLatticePaper.Construction.AlternateLadderExtension
import FLatticePaper.Construction.LadderRotation
import FLatticePaper.Plane.AlternatePeriods

namespace FLatticePaper.Construction

open Farey

/-- B8 uses the translated harmonic rotation and the additional affine term. -/
def rotateLadderAltField (den : ℤ) (field : Field) : Field := fun point =>
  rotateLadderField den (fun site => field (site - (2, 0))) point + (point.1 + 1)

private theorem rotateLadderAltField_eq (den : ℤ) (field : Field) (point : Site) :
    rotateLadderAltField den field point =
      field (QuarterTurn.counterclockwise.mapSite (2 * den - 2, 1) point) +
        (centeredQuarterTurnCorrection point + (point.1 + 1)) := by
  have hshift : QuarterTurn.counterclockwise.mapSite (2 * den, 1) point - (2, 0) =
      QuarterTurn.counterclockwise.mapSite (2 * den - 2, 1) point := by
    apply Prod.ext <;> dsimp [QuarterTurn.mapSite, QuarterTurn.turn] <;> omega
  simp only [rotateLadderAltField, rotateLadderField, hshift, add_assoc]

private theorem harmonic_ladderAltCorrection :
    Harmonic (fun point : Site => centeredQuarterTurnCorrection point + (point.1 + 1)) := by
  intro point
  have h := harmonic_centeredQuarterTurnCorrection point
  have hline : (incomingNeg point).1 + (incomingPos point).1 = 2 * point.1 := by
    by_cases he : EvenSite point
    · simp only [incomingNeg, incomingPos, if_pos he]
      omega
    · simp only [incomingNeg, incomingPos, if_neg he]
      omega
  simp only [laplacian] at h ⊢
  omega

theorem rotateLadderAltField_recurrent {den : ℤ} {field : Field}
    (hrec : Recurrent field) (hsuper : Superharmonic field) :
    Superharmonic (rotateLadderAltField den field) ∧ Recurrent (rotateLadderAltField den field) := by
  have hr := hrec.quarterTurn hsuper .counterclockwise (2 * den - 2, 1)
    (by change (2 * den - 2 + 1) % 2 ≠ 0; omega) harmonic_ladderAltCorrection
  have hf := funext (rotateLadderAltField_eq den field)
  simpa only [hf] using hr

/-- The B8 transverse constant after final centering. -/
def ladderEvenAltConstantV (den : ℤ) : ℤ := ladderEvenConstantV den - 1

theorem ladderEvenAltConstantV_eq (den : ℤ) : ladderEvenAltConstantV den = -den ^ 2 - 3 * den := by
  rw [ladderEvenAltConstantV, ladderEvenConstantV_eq]
  omega

theorem rotateLadderAltField_periods {den : ℤ} (heven : den % 2 = 0) {field : Field}
    (hperiod : HasGeneratorPeriods (Fraction.mk 1 den) field (-1) (ladderOddAltConstantV den)) :
    HasGeneratorPeriods (Fraction.mk 1 den).rotate (rotateLadderAltField den field) 0 (ladderEvenAltConstantV den) := by
  let shifted : Field := fun point => field (point - (2, 0))
  have htranslate (point step : Site) : point + step - (2, 0) = point - (2, 0) + step := by
    apply Prod.ext <;> dsimp <;> omega
  have hshift : HasGeneratorPeriods (Fraction.mk 1 den) shifted (-1) (ladderOddAltConstantV den - 2) := by
    constructor
    · intro point
      simp only [shifted, htranslate, hperiod.1]
    · intro point
      simp only [shifted, htranslate, hperiod.2, Fraction.transverseGrade, Prod.fst_sub, Prod.snd_sub,
        one_mul, sub_zero]
      ring
  have hrot := hasGeneratorPeriods_rotateLadderField heven hshift
  rw [show den + (ladderOddAltConstantV den - 2) + chooseTwo (den + 1) = -(den + 1) by
    unfold ladderOddAltConstantV; omega, sub_neg_eq_add] at hrot
  constructor
  · intro point
    have h := hrot.1 point
    rw [nearOneLadderDeck_eq heven] at h ⊢
    change rotateLadderField den shifted (point + (den + 1, den - 1)) +
      ((point + (den + 1, den - 1)).1 + 1) = rotateLadderField den shifted point + (point.1 + 1) + 0
    rw [h, Prod.fst_add]
    omega
  · intro point
    have h := hrot.2 point
    rw [nearOneLadderDeck_eq heven] at h ⊢
    change rotateLadderField den shifted (point + (-2, 2 * den)) + ((point + (-2, 2 * den)).1 + 1) =
      rotateLadderField den shifted point + (point.1 + 1) -
        (Fraction.mk 1 den).rotate.transverseGrade point + ladderEvenAltConstantV den
    rw [h, Prod.fst_add, ladderEvenAltConstantV]
    omega

theorem BaseMask.ladderEvenAlt_agrees_rotateLadderAltField {den : ℤ} (hden : BaseMask.ladderEvenAlt.Valid den)
    {field : Field} (hagree : (BaseMask.ladderOddAlt.raw den).Agrees field 0) :
    ((BaseMask.ladderEvenAlt.tile den hden).llCenter (BaseMask.ladderEvenAlt.tile_nonempty den hden)).Agrees
      (rotateLadderAltField den field) 0 := by
  let raw : Field := fun point =>
    field (2 * den - 1 - point.2, point.1 + 1) + (chooseTwo point.1 - (point.1 - point.2) ^ 2 / 4 + point.1 + 1)
  have hraw : (BaseMask.ladderEvenAlt.raw den).Agrees raw 0 := by
    intro point
    let pulled : (BaseMask.ladderOddAlt.raw den).sites := ⟨(2 * den - 1 - point.val.2, point.val.1 + 1),
      (BaseMask.mem_ladderEvenAlt_raw_pullback_iff point.val).mp point.property⟩
    have hpull := hagree pulled
    rw [BaseMask.ladderOddAlt_raw_height, add_zero] at hpull
    change BaseMask.ladderOddAltValue den (2 * den - 1 - point.val.2, point.val.1 + 1) =
      field (2 * den - 1 - point.val.2, point.val.1 + 1) at hpull
    rw [BaseMask.ladderEvenAlt_raw_height]
    change _ = raw point.val + 0
    simp only [raw, hpull, chooseTwo, add_zero]
  have hcenter := BaseMask.ladderEvenAlt_llCenter_agrees hden hraw
  have hchart : (fun point : Site => raw (point + (0, 1))) = rotateLadderAltField den field := by
    funext point
    rw [rotateLadderAltField_eq]
    have hpull : QuarterTurn.counterclockwise.mapSite (2 * den - 2, 1) point =
        (2 * den - 1 - (point.2 + 1), point.1 + 1) :=
      Prod.ext (by dsimp [QuarterTurn.mapSite, QuarterTurn.turn]; omega) rfl
    simp only [raw, hpull, centeredQuarterTurnCorrection, Prod.fst_add, Prod.snd_add, add_zero, add_assoc]
    rw [show point.1 - (point.2 + 1) = point.1 - point.2 - 1 by omega]
  rwa [hchart] at hcenter

theorem ladderEvenAlt_exists_extension {den : ℤ} (hden : BaseMask.ladderEvenAlt.Valid den) :
    ∃ field : Field,
      ((BaseMask.ladderEvenAlt.tile den hden).llCenter (BaseMask.ladderEvenAlt.tile_nonempty den hden)).Agrees field 0 ∧
      HasGeneratorPeriods (Fraction.mk 1 den).rotate field 0 (ladderEvenAltConstantV den) ∧
      HasQuadraticGrowth field (Fraction.mk 1 den).rotate.matrix := by
  obtain ⟨field, hagree, hperiod, _⟩ := ladderOddAlt_exists_extension hden
  have hrot := rotateLadderAltField_periods hden.2 hperiod
  exact ⟨rotateLadderAltField den field, BaseMask.ladderEvenAlt_agrees_rotateLadderAltField hden hagree,
    hrot, generator_periods_growth (ladder_rotate_inUnitInterval hden.1 hden.2) hrot⟩

theorem evaluateNative_twos_even_alternate_extension (extra : ℕ) :
    let word := (BaseRun.twos extra).word
    let den : ℤ := 2 * (extra : ℤ) + 3 + 1
    let fraction := (parentsAt word).current .even
    ∃ registers : TileRegisters, ∃ field : Field,
      evaluateNative word = .ok registers ∧ registers.alternate.currentEven.val.Agrees field 0 ∧
      HasGeneratorPeriods fraction field 0 (ladderEvenAltConstantV den) ∧
      HasQuadraticGrowth field fraction.matrix := by
  dsimp only
  rw [twos_current_even]
  have hvalid : BaseMask.ladderEvenAlt.Valid (2 * (extra : ℤ) + 3 + 1) := by
    change 4 ≤ 2 * (extra : ℤ) + 3 + 1 ∧ (2 * (extra : ℤ) + 3 + 1) % 2 = 0
    omega
  obtain ⟨field, hagree, hperiod, hgrowth⟩ := ladderEvenAlt_exists_extension hvalid
  exact ⟨(BaseRun.twos extra).registers.llCenter, field, evaluateNative_base _, hagree, hperiod, hgrowth⟩

private theorem not_integerAffine_of_even_period_increment {field : Field} (period : Site)
    (hcol : period.1 % 2 = 0) (hrow : period.2 % 2 = 0) (hinc : field period - field 0 = -1) :
    ¬ IntegerAffine field := by
  rintro ⟨gradient, constant, haffine⟩
  have hcol' : period.1 = 2 * (period.1 / 2) := by omega
  have hrow' : period.2 = 2 * (period.2 / 2) := by omega
  have heven : field period - field 0 =
      2 * (gradient.1 * (period.1 / 2) + gradient.2 * (period.2 / 2)) := by
    rw [haffine period, haffine 0]
    simp only [Prod.fst_zero, Prod.snd_zero, mul_zero, zero_add]
    linear_combination gradient.1 * hcol' + gradient.2 * hrow'
  omega

theorem ladderOddAlt_sub_standard_not_integerAffine {den : ℤ} (heven : den % 2 = 0)
    {standard alternate : Field} {constantV constantV' : ℤ}
    (hstandard : HasGeneratorPeriods (Fraction.mk 1 den) standard 0 constantV)
    (halternate : HasGeneratorPeriods (Fraction.mk 1 den) alternate (-1) constantV') :
    ¬ IntegerAffine (fun site => alternate site - standard site) := by
  have hs := hstandard.1 (0 : Site)
  have ha := halternate.1 (0 : Site)
  change standard (0 + (reciprocalLadderDeck den).kernel) = _ at hs
  change alternate (0 + (reciprocalLadderDeck den).kernel) = _ at ha
  rw [reciprocalLadderDeck_eq heven, zero_add] at hs ha
  change standard (2 * den, 2) = standard 0 + 0 at hs
  change alternate (2 * den, 2) = alternate 0 + (-1) at ha
  apply not_integerAffine_of_even_period_increment (2 * den, 2)
  · change (2 * den) % 2 = 0
    omega
  · change (2 : ℤ) % 2 = 0
    decide
  · omega

theorem ladderEvenAlt_sub_standard_not_integerAffine {den : ℤ} (heven : den % 2 = 0)
    {standard alternate : Field} {constantU constantU' : ℤ}
    (hstandard : HasGeneratorPeriods (Fraction.mk 1 den).rotate standard constantU (ladderEvenConstantV den))
    (halternate : HasGeneratorPeriods (Fraction.mk 1 den).rotate alternate constantU' (ladderEvenAltConstantV den)) :
    ¬ IntegerAffine (fun site => alternate site - standard site) := by
  have hs := hstandard.2 (0 : Site)
  have ha := halternate.2 (0 : Site)
  rw [nearOneLadderDeck_eq heven, zero_add] at hs ha
  simp only [Fraction.transverseGrade, Prod.fst_zero, Prod.snd_zero, mul_zero, sub_zero,
    ladderEvenAltConstantV] at hs ha
  apply not_integerAffine_of_even_period_increment (-2, 2 * den)
  · change (-2 : ℤ) % 2 = 0
    decide
  · change (2 * den) % 2 = 0
    omega
  · omega

end FLatticePaper.Construction
