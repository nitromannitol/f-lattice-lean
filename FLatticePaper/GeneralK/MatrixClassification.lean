import FLatticePaper.GeneralK.TightStabilizer
import FLatticePaper.GeneralK.TightWinding

namespace FLatticePaper.GeneralK

open Farey

private theorem exists_integralInputPotential_of_det_pos {k : ℤ} (hk : 2 ≤ k) (deck : PeriodDeck)
    (hdet : 0 < deck.det) (hphase : ∀ step ∈ deck.span, Retained k step) (negative positive : Field)
    (hneg : ∀ step ∈ deck.span, Function.Periodic negative step)
    (hpos : ∀ step ∈ deck.span, Function.Periodic positive step)
    (hfeasible : ∃ (potential : Site → ℝ) (slopeX slopeY : ℝ),
      SatisfiesInputLabels k negative positive potential ∧ HasDeckSlope deck potential slopeX slopeY) :
    ∃ (potential : Site → ℝ) (slopeX slopeY : ℚ),
      SatisfiesInputLabels k negative positive potential ∧ HasDeckSlope deck potential (slopeX : ℝ) (slopeY : ℝ) ∧
      ∀ step ∈ deck.span, ∃ increment : ℤ,
        (slopeX : ℝ) * (step.1 : ℝ) + (slopeY : ℝ) * (step.2 : ℝ) = (increment : ℝ) := by
  obtain ⟨initial, a, b, hs, hd⟩ := hfeasible
  have hne := feasiblePotentialParameters_nonempty hdet hs hd
  obtain ⟨param, hparam, u, hu, v, hv, hind, ⟨x, hx⟩, ⟨y, hy⟩⟩ :=
    exists_feasible_independent_tight_windings hdet hk hphase negative positive hneg hpos hne
  have hslope := hasDeckSlope_evaluatePotential hdet param
  have hall := tightReaches_all_periods_of_independent hslope hphase hneg hpos hdet.ne' hu hv hind hx hy
  have hkernel : deck.kernel ∈ deck.span := ⟨1, 0, by ext <;> simp [PeriodDeck.combine]⟩
  have htransverse : deck.transverse ∈ deck.span := ⟨0, 1, by ext <;> simp [PeriodDeck.combine]⟩
  obtain ⟨slopeX, slopeY, heqX, heqY, hinteger⟩ := hslope.exists_rat_of_tight_basis_walks hdet.ne'
    (hall deck.kernel hkernel) (hall deck.transverse htransverse)
  exact ⟨evaluatePotential hdet param, slopeX, slopeY, hparam.2, by rwa [heqX, heqY], hinteger⟩

/-- Every feasible periodic pair of integer input labels has a feasible
potential with integer affine increments on the given physical period deck. -/
theorem integralInputPotentials_of_two_le {k : ℤ} (hk : 2 ≤ k) : IntegralInputPotentials k := by
  intro deck hdet hphase negative positive hneg hpos hfeasible
  rcases lt_or_gt_of_ne hdet with hnegative | hpositive
  · let reversed : PeriodDeck := ⟨deck.transverse, deck.kernel⟩
    have hreverse : 0 < reversed.det := by
      have heq : reversed.det = -deck.det := by simp [PeriodDeck.det, reversed]; ring
      exact heq ▸ neg_pos.mpr hnegative
    have hspan : reversed.span = deck.span := by
      ext x
      constructor
      · rintro ⟨i, j, rfl⟩
        exact ⟨j, i, Prod.ext (by simp [PeriodDeck.combine, reversed, add_comm]) (by simp [PeriodDeck.combine, reversed, add_comm])⟩
      · rintro ⟨i, j, rfl⟩
        exact ⟨j, i, Prod.ext (by simp [PeriodDeck.combine, reversed, add_comm]) (by simp [PeriodDeck.combine, reversed, add_comm])⟩
    have hfeasible' : ∃ (potential : Site → ℝ) (slopeX slopeY : ℝ),
        SatisfiesInputLabels k negative positive potential ∧ HasDeckSlope reversed potential slopeX slopeY := by
      obtain ⟨potential, a, b, hs, ha⟩ := hfeasible
      exact ⟨potential, a, b, hs, fun step hstep => ha step (hspan ▸ hstep)⟩
    obtain ⟨potential, a, b, hs, ha, hb⟩ := exists_integralInputPotential_of_det_pos hk reversed hreverse
      (by rwa [hspan]) negative positive (by rwa [hspan]) (by rwa [hspan]) hfeasible'
    exact ⟨potential, a, b, hs, fun step hstep => ha step (hspan.symm ▸ hstep),
      fun step hstep => hb step (hspan.symm ▸ hstep)⟩
  · exact exists_integralInputPotential_of_det_pos hk deck hpositive hphase negative positive hneg hpos hfeasible

/-- The exact rational period realization for every allowed full-rank deck. -/
theorem rationalPeriodRealization_of_two_le {k : ℤ} (hk : 2 ≤ k) : RationalPeriodRealization k :=
  rationalPeriodRealization_of_integralInputPotentials hk (integralInputPotentials_of_two_le hk)

/-- The explicit rational column endpoint classifies its entire real slice. -/
theorem mem_growthSet_iff_le_cycleEndpoint {k : ℤ} (hk : 2 ≤ k) (b c : ℚ) (a : ℝ) :
    symmetricMatrix a (b : ℝ) (c : ℝ) ∈ growthSet k ↔ a ≤ cycleEndpoint k hk b c :=
  rationalSlice_iff_le_cycleEndpoint hk (rationalPeriodRealization_of_two_le hk) b c a

/-- The GeneralK parabolic classification for all real physical entries. -/
theorem mem_growthSet_iff_le_columnParabolic {k : ℤ} (hk : 2 ≤ k) (a b c : ℝ) :
    symmetricMatrix a b c ∈ growthSet k ↔ a ≤ sInf (parabolicValues (cycleEndpoint k hk) b c) :=
  mem_growthSet_iff_le_cycleParabolic hk (rationalPeriodRealization_of_two_le hk) a b c

/-- Both inclusions of the complete GeneralK matrix classification,
with irrational boundaries included by closure in the real matrix space. -/
theorem growthSet_eq_closure_columnCones {k : ℤ} (hk : 2 ≤ k) :
    growthSet k = closure (rationalConeUnion (cycleEndpoint k hk)) :=
  growthSet_eq_closure_cycleCones hk (rationalPeriodRealization_of_two_le hk)

end FLatticePaper.GeneralK
