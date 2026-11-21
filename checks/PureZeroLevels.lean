import FLatticePaper.Construction.PureZeroLevels
import FLatticePaper.Construction.LadderRank

namespace FLatticePaper.Checks

open Construction Farey

theorem root_standard_pair_additional_zeros :
    ∃ even odd : Field, Recurrent even ∧ Recurrent odd ∧
      (∀ site, 3 * site.2 - site.1 = 2 → even site = 0) ∧
      ∀ site, 2 * site.2 - site.1 = 2 → EvenSite site → odd site = 0 := by
  have hvalid : BaseMask.stairEven.Valid 3 := by simp [BaseMask.Valid]
  obtain ⟨field, hagree, hp, -, hs, hr⟩ := stairEven_exists_recurrent_extension hvalid
  have ⟨_, hrot⟩ := rotateStaircaseField_recurrent hvalid.2 hr hs
  refine ⟨field, rotateStaircaseField 3 field, hr, hrot, ?_, ?_⟩
  · intro site hgrade
    apply stairEven_additional_zero hvalid hagree hp
    change 3 * site.2 - 1 * site.1 = 3 - 1
    omega
  · intro site hgrade hphase
    apply rotateStaircaseField_additional_zero hvalid hagree hp site _ hphase
    change 2 * site.2 - 1 * site.1 = 3 - 1
    omega

theorem first_doubled_ladders_additional_zeros :
    ∃ odd even : Field, Recurrent odd ∧ Recurrent even ∧
      (∀ site, 4 * site.2 - site.1 = 4 → EvenSite site → odd site = 0) ∧
      ∀ site, 5 * site.2 - 3 * site.1 = 6 → even site = 0 := by
  have hvalid : BaseMask.ladderOdd.Valid 4 := by simp [BaseMask.Valid]
  obtain ⟨field, hagree, hp, -, hs, hr⟩ := ladderOdd_exists_recurrent_extension hvalid
  have ⟨_, hrot⟩ := rotateLadderField_recurrent (den := 4) hr hs
  refine ⟨field, rotateLadderField 4 field, hr, hrot, ?_, ?_⟩
  · intro site hgrade hphase
    apply ladderOdd_additional_zero hvalid hagree hp site _ hphase
    simpa only [Fraction.transverseGrade, one_mul] using hgrade
  · intro site hgrade
    apply rotateLadderField_additional_zero hvalid hagree hp site
    change 5 * site.2 - 3 * site.1 = 2 * 4 - 2
    omega

#print axioms root_standard_pair_additional_zeros
#print axioms first_doubled_ladders_additional_zeros

end FLatticePaper.Checks
