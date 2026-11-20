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

#print axioms PeriodDeck.exists_halfShiftedCell_representative
#print axioms stairEven_cover
#print axioms stairEvenAlt_cover
#print axioms evaluateNative_threes_even_covers
#print axioms long_pure_three_has_even_deck_cover

end FLatticePaper.Checks
