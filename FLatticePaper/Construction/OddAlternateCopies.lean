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

/-! ## The standard odd copies in their own chart -/

/-- The chart of the standard odd copy zero: `−kernel` of the even parent in phase one, zero in phase zero. Numerically the first
copy of every ordinary odd alternate is `planeTarget w .odd` read at `x − oddStdChart w` (scripts/odd_copy_gap.py). -/
def oddStdChart (word : Word) : Site :=
  if phase word = 1 then -(kernelJet (parentsAt word).even).1 else 0

/-- **The first copy of the odd ordinary alternate agrees with the raw odd target**, from the standard odd copy zero (its standard
identity in its own chart, named) and the shear identity between the raw target and the standard target on the copy's sites (named;
numerically constant on the copy for all 23 odd words of length at most three). The constants combine as `g − k`. -/
theorem ordinaryAlternate_odd_first_agrees (parents : TileParents) (beforePush : Word) (digit : Digit) {g k : ℤ}
    (hstd : (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0).val.Agrees
      (fun y => planeTarget (beforePush ++ [digit]) .odd (y - oddStdChart (beforePush ++ [digit]))) g)
    (hshear : ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0).val.sites,
      alternateOddRawTarget (beforePush ++ [digit]) s =
        planeTarget (beforePush ++ [digit]) .odd (s - oddStdChart (beforePush ++ [digit])) + k) :
    (ordinaryAlternateSchedule parents beforePush digit .odd).first.val.Agrees
      (alternateOddRawTarget (beforePush ++ [digit])) (g - k) := by
  rw [ordinaryAlternate_odd_first_eq]
  intro s
  have h1 : (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0).val.height s =
      planeTarget (beforePush ++ [digit]) .odd (s.1 - oddStdChart (beforePush ++ [digit])) + g := hstd s
  have h2 := hshear s.1 s.2
  rw [h1, h2]
  ring

/-- **A coincident copy of the odd ordinary alternate agrees with the raw odd target** in phase one (the copy in slot two is the
standard odd copy four), from the standard identity of the copy with `planeTarget` and the shear identity on its sites (both named). -/
theorem ordinaryAlternate_odd_copy_two_agrees (parents : TileParents) (word : Word) (h : phase word = 1) {g k : ℤ}
    (hstd : (ordinaryStandardCopy parents word .odd 4).val.Agrees (planeTarget word .odd) g)
    (hshear : ∀ s ∈ (ordinaryStandardCopy parents word .odd 4).val.sites,
      alternateOddRawTarget word s = planeTarget word .odd s + k) :
    (placedBySlot (alternateJets word .odd) (standardSources parents .even) 2).val.Agrees
      (alternateOddRawTarget word) (g - k) := by
  rw [ordinaryAlternate_odd_copy_two_eq parents word h]
  intro s
  have h1 : (ordinaryStandardCopy parents word .odd 4).val.height s = planeTarget word .odd s.1 + g := hstd s
  have h2 := hshear s.1 s.2
  rw [h1, h2]
  ring

/-- **A coincident copy of the odd ordinary alternate agrees with the raw odd target** in phase zero (the copy in slot four is the
standard odd copy five). -/
theorem ordinaryAlternate_odd_copy_four_agrees (parents : TileParents) (word : Word) (h : phase word = 0) {g k : ℤ}
    (hstd : (ordinaryStandardCopy parents word .odd 5).val.Agrees (planeTarget word .odd) g)
    (hshear : ∀ s ∈ (ordinaryStandardCopy parents word .odd 5).val.sites,
      alternateOddRawTarget word s = planeTarget word .odd s + k) :
    (placedBySlot (alternateJets word .odd) (standardSources parents .even) 4).val.Agrees
      (alternateOddRawTarget word) (g - k) := by
  rw [ordinaryAlternate_odd_copy_four_eq parents word h]
  intro s
  have h1 : (ordinaryStandardCopy parents word .odd 5).val.height s = planeTarget word .odd s.1 + g := hstd s
  have h2 := hshear s.1 s.2
  rw [h1, h2]
  ring

/-- The phase is zero or one. -/
theorem phase_eq_zero_or_one (word : Word) : phase word = 0 ∨ phase word = 1 := by
  unfold phase
  omega

/-- **The ordinary odd alternate agrees with its raw odd target**, with the first copy and the coincident copy (slot two in phase one,
slot four in phase zero) discharged from the standard odd copies, and the seventh copy from the donor induction. Named: the standard odd
identities of the copies in their charts (the first copy in `oddStdChart`, the coincident copies at zero chart), the shear identities
between the raw target and the standard target on those copies, the slots other than the coincident one, the donor induction and the
midpoint identity of the seventh copy, and the contacts. -/
theorem ordinaryAlternate_odd_identifies_copies (parents : TileParents) (beforePush : Word) (digit : Digit)
    (hnb : ¬ FLatticePaper.Tiles.Standard.IsBase (beforePush ++ [digit]))
    (context : String)
    (hstd0 : ∃ g : ℤ, (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0).val.Agrees
      (fun y => planeTarget (beforePush ++ [digit]) .odd (y - oddStdChart (beforePush ++ [digit]))) g)
    (hshear0 : ∃ k : ℤ, ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 0).val.sites,
      alternateOddRawTarget (beforePush ++ [digit]) s =
        planeTarget (beforePush ++ [digit]) .odd (s - oddStdChart (beforePush ++ [digit])) + k)
    (hco1 : phase (beforePush ++ [digit]) = 1 →
      (∃ g : ℤ, (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 4).val.Agrees
        (planeTarget (beforePush ++ [digit]) .odd) g) ∧
      (∃ k : ℤ, ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 4).val.sites,
        alternateOddRawTarget (beforePush ++ [digit]) s = planeTarget (beforePush ++ [digit]) .odd s + k))
    (hco0 : phase (beforePush ++ [digit]) = 0 →
      (∃ g : ℤ, (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 5).val.Agrees
        (planeTarget (beforePush ++ [digit]) .odd) g) ∧
      (∃ k : ℤ, ∀ s ∈ (ordinaryStandardCopy parents (beforePush ++ [digit]) .odd 5).val.sites,
        alternateOddRawTarget (beforePush ++ [digit]) s = planeTarget (beforePush ++ [digit]) .odd s + k))
    {g0 : ℤ} (hdonor : parents.alternateEven.val.Agrees (alternateTarget beforePush) g0)
    (hmid : ¬ FLatticePaper.Tiles.Standard.IsBase (beforePush ++ [digit]) → ∃ k : ℤ,
      ∀ s ∈ (alternateOddSeventhCopy parents beforePush digit).val.sites,
        alternateOddRawTarget (beforePush ++ [digit]) s =
          alternateTarget beforePush
              (s - ((seventhAlternateJet beforePush digit .odd).1 +
                alternateRestoration (beforePush ++ [digit]) .even)) +
            ((seventhAlternateJet beforePush digit .odd).2.1 * s.1 +
              (seventhAlternateJet beforePush digit .odd).2.2 * s.2) + k)
    (hslot : ∀ s ∈ afterSeventhAlternate .odd, (phase (beforePush ++ [digit]) = 1 → s ≠ 2) →
      (phase (beforePush ++ [digit]) = 0 → s ≠ 4) → ∃ g : ℤ,
      (placedBySlot (alternateJets (beforePush ++ [digit]) .odd) (standardSources parents .even) s).val.Agrees
        (alternateOddRawTarget (beforePush ++ [digit])) g)
    (hcon : HeightTile.OrderedContacts (ordinaryAlternateSchedule parents beforePush digit .odd).first.val.sites
      (ordinaryAlternateSchedule parents beforePush digit .odd).copies) :
    ∃ result, (ordinaryAlternateSchedule parents beforePush digit .odd).eval .tile context = .ok result ∧
      ∃ g : ℤ, result.val.Agrees
        (fun site => alternateOddRawTarget (beforePush ++ [digit]) (site +
          ((ordinaryAlternateSchedule parents beforePush digit .odd).raw hcon).val.boxOrigin
            ((ordinaryAlternateSchedule parents beforePush digit .odd).raw hcon).property)) g := by
  obtain ⟨g1, hg1⟩ := hstd0
  obtain ⟨k1, hk1⟩ := hshear0
  have hfirst : ∃ g : ℤ, (ordinaryAlternateSchedule parents beforePush digit .odd).first.val.Agrees
      (alternateOddRawTarget (beforePush ++ [digit])) g :=
    ⟨g1 - k1, ordinaryAlternate_odd_first_agrees parents beforePush digit hg1 hk1⟩
  have hslot' : ∀ s ∈ afterSeventhAlternate .odd, ∃ g : ℤ,
      (placedBySlot (alternateJets (beforePush ++ [digit]) .odd) (standardSources parents .even) s).val.Agrees
        (alternateOddRawTarget (beforePush ++ [digit])) g := by
    intro s hs
    rcases phase_eq_zero_or_one (beforePush ++ [digit]) with h0 | h1
    · by_cases h4 : s = 4
      · subst h4
        obtain ⟨⟨g, hg⟩, ⟨k, hk⟩⟩ := hco0 h0
        exact ⟨g - k, ordinaryAlternate_odd_copy_four_agrees parents (beforePush ++ [digit]) h0 hg hk⟩
      · exact hslot s hs (fun h => by rw [h0] at h; exact absurd h (by decide)) (fun _ => h4)
    · by_cases h2 : s = 2
      · subst h2
        obtain ⟨⟨g, hg⟩, ⟨k, hk⟩⟩ := hco1 h1
        exact ⟨g - k, ordinaryAlternate_odd_copy_two_agrees parents (beforePush ++ [digit]) h1 hg hk⟩
      · exact hslot s hs (fun _ => h2) (fun h => by rw [h1] at h; exact absurd h (by decide))
  have hseventh : ∃ g : ℤ, ((seventhAlternateJet beforePush digit .odd).place
      (FLatticePaper.Tiles.AlternateOrdinary.oldAlternate parents (beforePush ++ [digit]) .odd)).val.Agrees
      (alternateOddRawTarget (beforePush ++ [digit])) g := by
    obtain ⟨k, hk⟩ := hmid hnb
    exact ⟨g0 - k, alternateOddSeventhCopy_agrees_of_donor parents beforePush digit hdonor k hk⟩
  obtain ⟨gf, hgf⟩ := hfirst
  exact FLatticePaper.Tiles.AlternateAgreement.ordinaryAlternate_output_agrees_of_seven parents beforePush digit .odd
    context hgf hseventh hslot' hcon

end FLatticePaper.Construction
