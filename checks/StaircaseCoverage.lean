import FLatticePaper.Construction.StaircaseCoverage

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

end FLatticePaper.Checks
