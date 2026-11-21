import FLatticePaper.GeneralK.PeriodExtremum

namespace FLatticePaper.GeneralK.Checks

open Farey

private def threeDeck : PeriodDeck := ⟨(1, -1), (0, 3)⟩

private theorem threeDeck_det : 0 < threeDeck.det := by decide

theorem three_zero_labels_have_a_feasible_extremum :
    ∃ param ∈ feasiblePotentialParameters threeDeck_det 3 0 0, ∀ direction : PotentialParameters threeDeck,
      evaluatePotential threeDeck_det direction 0 = 0 →
      (∀ site sign, inputDifference threeDeck_det 3 param site sign = 0 →
        inputDifference threeDeck_det 3 direction site sign = 0) → direction = 0 := by
  have hphase : ∀ step ∈ threeDeck.span, Retained 3 step := by
    rintro _ ⟨i, j, rfl⟩
    change (i * 1 + j * 0 + (i * (-1) + j * 3)) % 3 = 0
    omega
  have hne := feasiblePotentialParameters_nonempty (k := 3) (negative := 0) (positive := 0)
    (potential := 0) (slopeX := 0) (slopeY := 0) threeDeck_det (fun _ => by simp) (fun _ _ _ => by simp)
  obtain ⟨param, hparam, hmax⟩ := exists_feasible_extremum threeDeck_det (by decide : (2 : ℤ) ≤ 3) hphase 0 0
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) hne
  refine ⟨param, hparam, fun direction hzero hdir => hmax direction hzero ?_⟩
  intro site sign htight
  apply hdir site sign
  simpa using htight

#print axioms isCompact_feasiblePotentialParameters
#print axioms exists_feasible_extremum
#print axioms three_zero_labels_have_a_feasible_extremum

end FLatticePaper.GeneralK.Checks
