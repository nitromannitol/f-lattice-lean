import FLatticePaper.Construction.StaircaseRotation
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
