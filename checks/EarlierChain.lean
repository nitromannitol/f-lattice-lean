import FLatticePaper.Construction.StaircaseRotation
import FLatticePaper.Construction.StaircaseStrips
import FLatticePaper.Construction.LadderRotation
import FLatticePaper.Plane.EarlierChainPrice

open FLatticePaper FLatticePaper.Construction FLatticePaper.Farey

/-- The actual two root heights give one constant for either creator digit
and every length of the succeeding run of threes. -/
theorem root_donorPrice_constant (replaceEven : Bool) (steps : ℕ) :
    let current := parentsAt (donorWord [] replaceEven steps)
    let orientation := current.odd.det current.even
    ∃ reciprocal donor : Field,
      (BaseMask.stairEven.raw 3).Agrees reciprocal 0 ∧
      ((BaseMask.stairOdd.tile 3 (by simp [BaseMask.Valid])).llCenter
        (BaseMask.stairOdd.tile_nonempty 3 (by simp [BaseMask.Valid]))).Agrees donor 0 ∧
      ∃ value : ℤ, ∀ site,
        donorPrice donor current.even orientation 0 site +
          earlierChainPrice reciprocal (parentsAt []).odd ((parentsAt []).odd.det (parentsAt []).even) orientation
            (QuarterTurn.counterclockwise.mapSite (0, -1) site) = value := by
  dsimp only
  have hvalid : BaseMask.stairEven.Valid 3 := by simp [BaseMask.Valid]
  obtain ⟨reciprocal, hagree, hperiod, _⟩ := stairEven_exists_extension hvalid
  refine ⟨reciprocal, rotateStaircaseField 3 reciprocal, hagree,
    BaseMask.stairOdd_agrees_rotateStaircaseField hvalid hagree, ?_⟩
  exact donorPrice_add_earlierChainPrice [] replaceEven steps reciprocal (rotateStaircaseField 3 reciprocal)
    0 (stairEvenConstantV 3) 0 hperiod (rotateStaircaseField_earlierChain (by decide) hperiod)

#print axioms earlierChain_shift_eq_modified
#print axioms donorPrice_add_earlierChainPrice
#print axioms root_donorPrice_constant

/-- The positive pure-3 odd ladder and its reflected pure-2 even ladder
supply the genuine earlier price for both creator roles. -/
theorem pureThree_donorPrice_constant (extra : ℕ) (replaceEven : Bool) (steps : ℕ) :
    let origin := (BaseRun.threes extra).word
    let den : ℤ := 2 * (extra : ℤ) + 3 + 1
    let current := parentsAt (donorWord origin replaceEven steps)
    let earlier := parentsAt (origin.map Digit.swapTwoThree)
    let orientation := current.odd.det current.even
    let oldOrientation := (parentsAt origin).odd.det (parentsAt origin).even
    let hvalid : BaseMask.ladderEven.Valid den := by change 4 ≤ den ∧ den % 2 = 0; dsimp [den]; omega
    ∃ oddField evenField : Field,
      (BaseMask.ladderOdd.raw den).Agrees oddField 0 ∧
      ((BaseMask.ladderEven.tile den hvalid).llCenter (BaseMask.ladderEven.tile_nonempty den hvalid)).Agrees evenField 0 ∧
      ∃ value : ℤ, ∀ site,
        donorPrice oddField current.even orientation 0 site +
          earlierChainPrice evenField earlier.odd oldOrientation orientation
            (QuarterTurn.counterclockwise.mapSite (0, -1) site) = value := by
  let origin := (BaseRun.threes extra).word
  let den : ℤ := 2 * (extra : ℤ) + 3 + 1
  have hvalid : BaseMask.ladderOdd.Valid den := by
    change 4 ≤ den ∧ den % 2 = 0
    dsimp [den]
    omega
  obtain ⟨oddField, hagree, hperiod, _⟩ := ladderOdd_exists_extension hvalid
  let evenField := rotateLadderField den oddField
  have hjet := rotateLadderField_periods hvalid.2 hperiod
  have hframe := (parentsAt_valid origin).rotate_current_odd
  rw [rotate_parentsAt, threes_current_odd] at hframe
  change (Fraction.mk 1 den).rotate = ((parentsAt (origin.map Digit.swapTwoThree)).current .even) at hframe
  rw [hframe] at hjet
  refine ⟨oddField, evenField, hagree, BaseMask.ladderEven_agrees_rotateLadderField hvalid hagree, ?_⟩
  exact donorPrice_add_earlierChainPrice origin replaceEven steps evenField oddField 0 (ladderEvenConstantV den) 0
    hjet (ladderOdd_earlierChain hvalid hagree hperiod)

#print axioms pureThree_donorPrice_constant

theorem reciprocal_root_zero_at_upper_transverse_edge :
    ∃ field : Field, (BaseMask.stairEven.raw 3).Agrees field 0 ∧ Recurrent field ∧
      ∀ y : ℤ, field (3 * y + 6, y) = 0 := by
  have hvalid : BaseMask.stairEven.Valid 3 := by simp [BaseMask.Valid]
  obtain ⟨field, hagree, hperiod, _, _, hrec⟩ := stairEven_exists_recurrent_extension hvalid
  exact ⟨field, hagree, hrec, fun y =>
    stairEven_eq_zero_of_transverse hvalid hagree hperiod (3 * y + 6, y) (by dsimp; omega) (by dsimp; omega)⟩

#print axioms stairEven_eq_zero_of_transverse
#print axioms reciprocal_root_zero_at_upper_transverse_edge

theorem reciprocal_root_harmonic_along_transverse_period :
    ∃ field : Field, (BaseMask.stairEven.raw 3).Agrees field 0 ∧ Recurrent field ∧
      ∀ j : ℤ, field (-2 * j, 4 * j) = centeredQuarterTurnCorrection (-2 * j, 4 * j) := by
  have hvalid : BaseMask.stairEven.Valid 3 := by simp [BaseMask.Valid]
  obtain ⟨field, hagree, hperiod, _, _, hrec⟩ := stairEven_exists_recurrent_extension hvalid
  refine ⟨field, hagree, hrec, fun j => ?_⟩
  exact stairEven_eq_harmonic_of_longitudinal hvalid hagree hperiod (-2 * j, 4 * j) (by dsimp; omega) (by dsimp; omega)

#print axioms stairEven_eq_harmonic_of_longitudinal
#print axioms reciprocal_root_harmonic_along_transverse_period
