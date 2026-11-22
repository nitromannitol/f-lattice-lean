import FLatticePaper.Construction.AlternateIdentification

/-! # The copies of the ordinary odd alternate (task 46)

The odd alternate schedule of `w` places the same six jets as the standard odd schedule in three slots, with the same donors:

* the first copy (slot 0) is the standard odd copy 0 (`alternateJets_odd_zero_eq`, donor `parents.even` in both);
* in phase one, the copy in slot 2 is the standard odd copy 4 (both at the zero jet, donor `parents.odd`);
* in phase zero, the copy in slot 4 is the standard odd copy 5 (both at the jet `eT`, donor `parents.odd`).

These three are the same tiles, so their identities are those of the standard odd copies. The standard odd copies agree with the
standard odd target `quarter(F(swap w)) + h0` shifted by the llCenter chart and the slope (`alternateOddPlane`); on the branch where
the gap of the swapped word is at most one, this is the raw odd alternate target `alternateOddRawTarget` (the alternate midpoint is the
standard field there). The other copies (slots 1, 3, 5 and the other phase's copy) are not standard copies and stay named. -/

namespace FLatticePaper.Construction

open Farey FLatticePaper FLatticePaper.Induction HeightTile

/-! ## The jets -/

theorem alternateJets_odd_zero_eq (word : Word) : alternateJets word .odd 0 = standardJets word .odd 0 := by
  by_cases h : phase word = 0 <;> simp [alternateJets, standardJets, h, doubleFirst, doubleLast]

theorem alternateJets_odd_phase_one_two_eq (word : Word) (h : phase word = 1) :
    alternateJets word .odd 2 = standardJets word .odd 4 := by
  simp [alternateJets, standardJets, h, doubleFirst, doubleLast]

theorem alternateJets_odd_phase_zero_four_eq (word : Word) (h : phase word = 0) :
    alternateJets word .odd 4 = standardJets word .odd 5 := by
  simp [alternateJets, standardJets, h, doubleFirst, doubleLast]

/-! ## The tiles -/

/-- The first copy of the odd ordinary alternate is the first copy of the odd ordinary standard. -/
theorem ordinaryAlternate_odd_first_eq (parents : TileParents) (beforePush : Word) (digit : Digit) :
    (ordinaryAlternateSchedule parents beforePush digit .odd).first =
      ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0 := by
  have hj := alternateJets_odd_zero_eq (beforePush ++ [digit])
  have hs : standardSources parents .even 0 = standardSources parents .odd 0 := rfl
  show placedBySlot (alternateJets (beforePush ++ [digit]) .odd) (standardSources parents .even) 0 =
    placedBySlot (standardJets (beforePush ++ [digit]) .odd) (standardSources parents .odd) 0
  unfold placedBySlot
  rw [hj, hs]

/-- In phase one, the copy in slot two of the odd alternate is the standard odd copy four. -/
theorem ordinaryAlternate_odd_copy_two_eq (parents : TileParents) (word : Word) (h : phase word = 1) :
    placedBySlot (alternateJets word .odd) (standardSources parents .even) 2 =
      ordinaryStandardCopy parents word .odd 4 := by
  have hs : standardSources parents .even 2 = standardSources parents .odd 4 := rfl
  unfold ordinaryStandardCopy
  unfold placedBySlot
  rw [alternateJets_odd_phase_one_two_eq word h, hs]

/-- In phase zero, the copy in slot four of the odd alternate is the standard odd copy five. -/
theorem ordinaryAlternate_odd_copy_four_eq (parents : TileParents) (word : Word) (h : phase word = 0) :
    placedBySlot (alternateJets word .odd) (standardSources parents .even) 4 =
      ordinaryStandardCopy parents word .odd 5 := by
  have hs : standardSources parents .even 4 = standardSources parents .odd 5 := rfl
  unfold ordinaryStandardCopy
  unfold placedBySlot
  rw [alternateJets_odd_phase_zero_four_eq word h, hs]

/-! ## The standard odd target, shifted by the chart, and the branch -/

/-- The standard odd target of the word in the llCenter chart: `quarter(F(swap w))` read at `x − δ`, plus the slope. It is the
standard odd plane target `planeTarget w .odd` shifted by the chart offset `δ` and the transverse slope of the odd parent. -/
noncomputable def alternateOddPlane (word : Word) : Field := fun y =>
  quarterTurnField (standardField (word.map Digit.swapTwoThree)) (y - alternateOddDelta word) +
    ((alternateOddSlope word).1 * y.1 + (alternateOddSlope word).2 * y.2)

/-- On the branch where the swapped word's gap at the point of the quarter turn is in `[0, 1]`, the raw odd alternate target is the
shifted standard odd target. -/
theorem alternateOddRawTarget_eq_of_branch (word : Word) (x : Site)
    (hlo : 0 ≤ standardField (word.map Digit.swapTwoThree)
        (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word)) -
      standardField (word.map Digit.swapTwoThree)
        (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word) +
          alternateSigma (word.map Digit.swapTwoThree)))
    (hhi : standardField (word.map Digit.swapTwoThree)
        (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word)) -
      standardField (word.map Digit.swapTwoThree)
        (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word) +
          alternateSigma (word.map Digit.swapTwoThree)) ≤ 1) :
    alternateOddRawTarget word x = alternateOddPlane word x := by
  unfold alternateOddRawTarget alternateOddPlane quarterTurnField
  have hmin := alternateTarget_eq_min (word := word.map Digit.swapTwoThree)
    (QuarterTurn.counterclockwise.mapSite (0, -1) (x - alternateOddDelta word)) hlo (by omega)
  rw [hmin, min_eq_left (by omega)]

/-- A tile that is the shifted standard odd target on its sites agrees with the raw odd alternate target on the branch. -/
theorem HeightTile.Agrees.alternateOddRawTarget_of_branch {word : Word} {tile : HeightTile Site} {g : ℤ}
    (h : tile.Agrees (alternateOddPlane word) g)
    (hbr : ∀ s ∈ tile.sites,
      0 ≤ standardField (word.map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) (s - alternateOddDelta word)) -
        standardField (word.map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) (s - alternateOddDelta word) +
            alternateSigma (word.map Digit.swapTwoThree)) ∧
      standardField (word.map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) (s - alternateOddDelta word)) -
        standardField (word.map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) (s - alternateOddDelta word) +
            alternateSigma (word.map Digit.swapTwoThree)) ≤ 1) :
    tile.Agrees (alternateOddRawTarget word) g := by
  intro s
  have hb := hbr s.1 s.2
  rw [h s, alternateOddRawTarget_eq_of_branch word s.1 hb.1 hb.2]

/-- The first copy of the odd ordinary alternate agrees with the raw odd target, from the standard odd copy zero and the branch. -/
theorem ordinaryAlternate_odd_first_agrees (parents : TileParents) (beforePush : Word) (digit : Digit) {g : ℤ}
    (hstd : (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0).val.Agrees
      (alternateOddPlane (beforePush ++ [digit])) g)
    (hbr : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0).val.sites,
      0 ≤ standardField ((beforePush ++ [digit]).map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) (s - alternateOddDelta (beforePush ++ [digit]))) -
        standardField ((beforePush ++ [digit]).map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) (s - alternateOddDelta (beforePush ++ [digit])) +
            alternateSigma ((beforePush ++ [digit]).map Digit.swapTwoThree)) ∧
      standardField ((beforePush ++ [digit]).map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) (s - alternateOddDelta (beforePush ++ [digit]))) -
        standardField ((beforePush ++ [digit]).map Digit.swapTwoThree)
          (QuarterTurn.counterclockwise.mapSite (0, -1) (s - alternateOddDelta (beforePush ++ [digit])) +
            alternateSigma ((beforePush ++ [digit]).map Digit.swapTwoThree)) ≤ 1) :
    (ordinaryAlternateSchedule parents beforePush digit .odd).first.val.Agrees
      (alternateOddRawTarget (beforePush ++ [digit])) g := by
  rw [ordinaryAlternate_odd_first_eq]
  exact HeightTile.Agrees.alternateOddRawTarget_of_branch hstd hbr

end FLatticePaper.Construction
