import FLatticePaper.Farey.PeriodDeck
import FLatticePaper.Plane.BandBurn
import Mathlib.Algebra.Ring.Periodic

namespace FLatticePaper

open Farey

/-- Every class of the physical deck meets a given band. The coefficient
of the primary generator in the gap character is minus one. -/
theorem exists_band_site_of_primitiveDrift {deck : PeriodDeck} (hdet : deck.det ≠ 0) {gap : Field}
    {pitch : ℤ} (hdrift : ∀ site i j, gap (site + deck.combine i j) = gap site - i + pitch * j)
    (representative : Site) : ∃ site, gap site = 0 ∧ deck.classCode site = deck.classCode representative := by
  refine ⟨representative + deck.combine (gap representative) 0, by rw [hdrift]; simp, ?_⟩
  apply (deck.classCode_eq_iff hdet _ _).mpr
  rw [add_sub_cancel_left]
  exact ⟨gap representative, 0, rfl⟩

/-- Within the band, equality of physical deck classes means exactly an
integer translate by the band's winding period. -/
theorem classCode_eq_on_band_iff {deck : PeriodDeck} (hdet : deck.det ≠ 0) {gap : Field}
    {pitch : ℤ} (hdrift : ∀ site i j, gap (site + deck.combine i j) = gap site - i + pitch * j)
    {first second : Site} (hfirst : gap first = 0) (hsecond : gap second = 0) :
    deck.classCode first = deck.classCode second ↔ ∃ j : ℤ, first = second + j • deck.combine pitch 1 := by
  have hmultiple (j : ℤ) : j • deck.combine pitch 1 = deck.combine (pitch * j) j := by
    apply Prod.ext <;> (simp [PeriodDeck.combine]; ring)
  constructor
  · intro heq
    obtain ⟨i, j, hstep⟩ := (deck.classCode_eq_iff hdet _ _).mp heq
    have hreconstruct : first = second + deck.combine i j := by
      rw [← hstep, add_comm second, sub_add_cancel]
    have hgap := hdrift second i j
    rw [← hreconstruct, hfirst, hsecond] at hgap
    have hi : i = pitch * j := by omega
    exact ⟨j, by rw [hmultiple, ← hi, ← hreconstruct]⟩
  · rintro ⟨j, rfl⟩
    apply (deck.classCode_eq_iff hdet _ _).mpr
    rw [add_sub_cancel_left, hmultiple]
    exact ⟨pitch * j, j, rfl⟩

/-- A periodic tie rank on the actual winding period yields the complete
finite band burn, with classes indexed by physical deck codes. -/
theorem exists_leftThreshold_bandBurnOrder_deck {α : Type*} [LinearOrder α] {first second : Field}
    {firstRank secondRank : Site → α} (level : ℤ) (hunit : HasUnitSlip first second)
    (hfirst : IsConstrainedBurningRank first firstRank
      (fun center input => slipIncrement first second center input ≤ 0))
    (hsecond : IsConstrainedBurningRank second secondRank
      (fun center input => 0 ≤ slipIncrement first second center input))
    (deck : PeriodDeck) (hdet : 0 < deck.det) (pitch : ℤ)
    (hdrift : ∀ site i j, thresholdGap first second level (site + deck.combine i j) =
      thresholdGap first second level site - i + pitch * j)
    (hrank : Function.Periodic firstRank (deck.combine pitch 1)) :
    ∃ order, BandBurns (thresholdMin first second level) (thresholdGap first second level)
      deck.classCode (deck.residueSquare.image deck.classCode) order := by
  classical
  let gap := thresholdGap first second level
  let rankOnClass (cell : ℤ × ℤ) : α :=
    if h : ∃ site, gap site = 0 ∧ deck.classCode site = cell then firstRank h.choose else firstRank 0
  refine exists_leftThreshold_bandBurnOrder level hunit hfirst hsecond deck.classCode rankOnClass
    (deck.residueSquare.image deck.classCode) (fun site htie _ => ?_)
  have hsite : ∃ point, gap point = 0 ∧ deck.classCode point = deck.classCode site := ⟨site, htie, rfl⟩
  change firstRank site = rankOnClass (deck.classCode site)
  dsimp only [rankOnClass]
  rw [dif_pos hsite]
  obtain ⟨j, hshift⟩ := (classCode_eq_on_band_iff (ne_of_gt hdet) hdrift htie hsite.choose_spec.1).mp
    hsite.choose_spec.2.symm
  exact (congrArg firstRank hshift).trans ((hrank.zsmul j) hsite.choose)

end FLatticePaper
