import FLatticePaper.Construction.StaircaseLaplacian

namespace FLatticePaper.Checks

open Construction Farey

theorem long_pure_three_has_even_deck_cover :
    let word := List.replicate 200 .three
    let deck := (parentsAt word).current .even |>.modifiedDeck
    ∃ registers, evaluateNative word = .ok registers ∧
      deck.Covers registers.standard.currentEven.val.sites ∧
      deck.Covers registers.alternate.currentEven.val.sites :=
  evaluateNative_threes_even_covers 199

theorem long_pure_two_has_odd_deck_cover :
    let word := List.replicate 200 .two
    let deck := (parentsAt word).current .odd |>.modifiedDeck
    ∃ registers, evaluateNative word = .ok registers ∧
      deck.Covers registers.standard.currentOdd.val.sites ∧
      deck.Covers registers.alternate.currentOdd.val.sites :=
  evaluateNative_twos_odd_covers 199

theorem reciprocal_staircase_has_its_prescribed_plane_extension :
    ∃ field : Field, (BaseMask.stairEven.raw 201).Agrees field 0 ∧
      HasGeneratorPeriods ⟨1, 201⟩ field 0 (-20502) ∧
      HasQuadraticGrowth field (Fraction.mk 1 201).matrix := by
  have h := stairEven_exists_extension (den := 201) (by simp [BaseMask.Valid])
  rw [stairEvenConstantV_eq] at h
  exact h

theorem reciprocal_staircase_has_binary_plane_extension_at_three :
    ∃ field : Field, (BaseMask.stairEven.raw 3).Agrees field 0 ∧
      HasGeneratorPeriods ⟨1, 3⟩ field 0 (-9) ∧
      HasQuadraticGrowth field (Fraction.mk 1 3).matrix ∧
      ∀ point, laplacian field point = -1 ∨ laplacian field point = 0 := by
  have h := stairEven_exists_binary_extension (den := 3) (by simp [BaseMask.Valid])
  rw [stairEvenConstantV_eq] at h
  exact h

#print axioms PeriodDeck.exists_halfShiftedCell_representative
#print axioms stairEven_cover
#print axioms stairEvenAlt_cover
#print axioms evaluateNative_threes_even_covers
#print axioms long_pure_three_has_even_deck_cover
#print axioms BaseMask.mem_stairOdd_raw_iff
#print axioms BaseMask.mem_stairOddAlt_raw_iff
#print axioms stairOdd_cover
#print axioms stairOddAlt_cover
#print axioms evaluateNative_twos_odd_covers
#print axioms long_pure_two_has_odd_deck_cover
#print axioms HeightTile.exists_extension_of_respectsPeriods
#print axioms stairEven_overlap_indices
#print axioms stairEven_respectsPeriods
#print axioms stairEven_exists_extension
#print axioms reciprocal_staircase_has_its_prescribed_plane_extension
#print axioms stairEven_reflection
#print axioms stairEven_laplacian_on_raw
#print axioms laplacian_periodic_of_generatorPeriods
#print axioms stairEven_exists_binary_extension
#print axioms reciprocal_staircase_has_binary_plane_extension_at_three

end FLatticePaper.Checks
