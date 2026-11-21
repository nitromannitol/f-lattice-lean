import FLatticePaper.Plane.BandDeck

namespace FLatticePaper.Checks

private def zeroSheet : Field := fun _ => 0

private def diagonalSheet : Field := fun site => site.1 + site.2

private theorem diagonal_neg (site : Site) :
    diagonalSheet (incomingNeg site) = diagonalSheet site - 1 := by
  by_cases heven : EvenSite site <;> simp [diagonalSheet, incomingNeg, heven] <;> omega

private theorem diagonal_pos (site : Site) :
    diagonalSheet (incomingPos site) = diagonalSheet site + 1 := by
  by_cases heven : EvenSite site <;> simp [diagonalSheet, incomingPos, heven] <;> omega

private theorem diagonal_unit : HasUnitSlip zeroSheet diagonalSheet := by
  intro center input hinput
  rcases hinput with rfl | rfl
  · simp only [slipIncrement, zeroSheet, diagonal_neg]
    omega
  · simp only [slipIncrement, zeroSheet, diagonal_pos]
    omega

private theorem diagonal_left :
    IsConstrainedBurningRank zeroSheet (fun site => -diagonalSheet site)
      (fun center input => slipIncrement zeroSheet diagonalSheet center input ≤ 0) := by
  intro center
  right
  refine ⟨rfl, Or.inr ⟨?_, ?_⟩⟩ <;>
    simp only [slipIncrement, zeroSheet, diagonal_pos] <;> omega

private theorem diagonal_right :
    IsConstrainedBurningRank diagonalSheet diagonalSheet
      (fun center input => 0 ≤ slipIncrement zeroSheet diagonalSheet center input) := by
  intro center
  right
  refine ⟨?_, Or.inl ⟨?_, ?_⟩⟩ <;>
    simp only [laplacian, slipIncrement, zeroSheet, diagonal_neg, diagonal_pos] <;> omega

theorem diagonalThreshold_comparison {competitor : Field} (level : ℤ)
    (sites : Finset Site) (bound : ℤ) (hf : ∀ site ∈ sites, laplacian competitor site ≤ 0)
    (hb : ∀ site ∈ incomingBoundary sites,
      thresholdMin zeroSheet diagonalSheet level site - competitor site ≤ bound) :
    ∀ site ∈ sites, thresholdMin zeroSheet diagonalSheet level site - competitor site ≤ bound :=
  (isBurningRank_leftThreshold level diagonal_unit diagonal_left diagonal_right).finiteComparison
    sites bound hf hb

/-- The diagonal tie band is a single class along its period `(1,-1)`. -/
theorem diagonalThreshold_bandBurn (level : ℤ) :
    ∃ order, BandBurns (thresholdMin zeroSheet diagonalSheet level)
      (thresholdGap zeroSheet diagonalSheet level) (fun _ => ()) {()} order := by
  apply exists_rightThreshold_bandBurnOrder level diagonal_unit diagonal_left diagonal_right
    _ (fun _ => -level)
  intro site htie _
  dsimp [thresholdGap, zeroSheet] at htie
  omega

private def diagonalDeck : Farey.PeriodDeck := ⟨(0, 1), (-2, 0)⟩

/-- The same plane example burns the actual two classes for the winding
period `(-2,2)`, while keeping both physical input slots. -/
theorem diagonalThreshold_bandBurn_deck (level : ℤ) :
    ∃ order, BandBurns (thresholdMin zeroSheet diagonalSheet level)
      (thresholdGap zeroSheet diagonalSheet level) diagonalDeck.classCode
        (diagonalDeck.residueSquare.image diagonalDeck.classCode) order := by
  apply exists_leftThreshold_bandBurnOrder_deck level diagonal_unit diagonal_left diagonal_right diagonalDeck (by decide) 2
  · intro site i j
    dsimp [thresholdGap, zeroSheet, diagonalSheet, diagonalDeck, Farey.PeriodDeck.combine]
    omega
  · intro site
    dsimp [diagonalSheet, diagonalDeck, Farey.PeriodDeck.combine]
    omega

example : laplacian (thresholdMin zeroSheet diagonalSheet 0) (0, 0) = -1 := by decide

#print axioms isBurningRank_leftThreshold
#print axioms isBurningRank_rightThreshold
#print axioms leftThresholdRank_lt_iff_of_tie
#print axioms rightThresholdRank_lt_iff_of_tie
#print axioms exists_leftThreshold_bandBurnOrder
#print axioms exists_rightThreshold_bandBurnOrder
#print axioms diagonalThreshold_comparison
#print axioms diagonalThreshold_bandBurn
#print axioms classCode_eq_on_band_iff
#print axioms exists_leftThreshold_bandBurnOrder_deck
#print axioms diagonalThreshold_bandBurn_deck

end FLatticePaper.Checks
