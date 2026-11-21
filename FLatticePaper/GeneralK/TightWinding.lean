import FLatticePaper.GeneralK.TightGraph

namespace FLatticePaper.GeneralK

open Farey

private def tightWindings (deck : PeriodDeck) (k : ℤ) (negative positive : Field) (potential : Site → ℝ) : Set Site :=
  {step | step ∈ deck.span ∧ ∃ site, TightReaches k negative positive potential site (site + step)}

private theorem exists_annihilator_of_dependent (steps : Set Site)
    (hdep : ∀ u ∈ steps, ∀ v ∈ steps, u.1 * v.2 - u.2 * v.1 = 0) :
    ∃ a b : ℝ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ step ∈ steps, a * (step.1 : ℝ) + b * (step.2 : ℝ) = 0 := by
  by_cases h : ∃ u ∈ steps, u ≠ 0
  · obtain ⟨u, hu, hu'⟩ := h
    refine ⟨-(u.2 : ℝ), (u.1 : ℝ), ?_, fun v hv => ?_⟩
    · by_contra! hz
      apply hu'
      apply Prod.ext
      · exact_mod_cast hz.2
      · exact_mod_cast neg_eq_zero.mp hz.1
    · have e : (u.1 : ℝ) * (v.2 : ℝ) - (u.2 : ℝ) * (v.1 : ℝ) = 0 := by exact_mod_cast hdep u hu v hv
      linear_combination e
  · refine ⟨1, 0, Or.inl one_ne_zero, fun v hv => ?_⟩
    have hz : v = 0 := by by_contra hne; exact h ⟨v, hv, hne⟩
    simp [hz]

/-- An annihilator of tight windings lifts to a deck-slope perturbation
which is constant along every tight component. -/
private theorem exists_constant_on_tight_components {deck : PeriodDeck} {k : ℤ} {negative positive : Field}
    {potential : Site → ℝ} {slopeX slopeY a b : ℝ} (hslope : HasDeckSlope deck potential slopeX slopeY)
    (hphase : ∀ step ∈ deck.span, Retained k step) (hneg : ∀ step ∈ deck.span, Function.Periodic negative step)
    (hpos : ∀ step ∈ deck.span, Function.Periodic positive step)
    (hzero : ∀ step ∈ tightWindings deck k negative positive potential, a * (step.1 : ℝ) + b * (step.2 : ℝ) = 0) :
    ∃ direction : Site → ℝ, HasDeckSlope deck direction a b ∧
      ∀ x y, TightReaches k negative positive potential x y → direction x = direction y := by
  classical
  let reaches := TightReaches k negative positive potential
  let periods := periodSubgroup deck
  let tilt (step : Site) := a * (step.1 : ℝ) + b * (step.2 : ℝ)
  have slide {x y step : Site} (h : reaches x y) (hper : step ∈ deck.span) : reaches (x + step) (y + step) :=
    h.add_of_period (hphase _ hper) (hslope _ hper) (hneg _ hper) (hpos _ hper)
  let orbit : Setoid Site := by
    refine ⟨fun x y => ∃ shift ∈ deck.span, reaches x (y + shift), ?_⟩
    constructor
    · intro x
      exact ⟨0, periods.zero_mem, by simp only [add_zero]; exact .refl⟩
    · intro x y hxy
      obtain ⟨shift, hmem, h⟩ := hxy
      have hnegmem : -shift ∈ deck.span := periods.neg_mem hmem
      exact ⟨-shift, hnegmem, by simpa only [add_neg_cancel_right] using (slide h hnegmem).symm⟩
    · intro x y z hxy hyz
      obtain ⟨p, hp, h₁⟩ := hxy
      obtain ⟨q, hq, h₂⟩ := hyz
      exact ⟨q + p, periods.add_mem hq hp, by simpa only [add_assoc] using h₁.trans (slide h₂ hp)⟩
  let representative (site : Site) := (Quotient.mk orbit site).out
  have hrepresentative (site : Site) : orbit.r (representative site) site :=
    Quotient.exact (Quotient.out_eq (Quotient.mk orbit site))
  have hsame {x y : Site} (h : orbit.r x y) : representative x = representative y :=
    congrArg Quotient.out (Quotient.sound h)
  have hchoice (site : Site) : ∃ shift ∈ deck.span, reaches (representative site) (site + shift) := hrepresentative site
  choose shift hspan hreach using hchoice
  let direction (site : Site) := -tilt (shift site)
  have hcompare (x y : Site) (h : reaches x y) {step : Site} (hstep : step ∈ deck.span) (hy : y = x + step) :
      tilt step = 0 := hzero step ⟨hstep, x, hy ▸ h⟩
  refine ⟨direction, ?_, ?_⟩
  · intro step hmem site
    have hsame' : representative site = representative (site + step) := by
      apply hsame
      exact ⟨-step, periods.neg_mem hmem, by rw [add_neg_cancel_right]⟩
    have hnext := hreach (site + step)
    rw [← hsame'] at hnext
    let difference := step + shift (site + step) - shift site
    have hd : difference ∈ deck.span := periods.sub_mem (periods.add_mem hmem (hspan (site + step))) (hspan site)
    have heq : site + step + shift (site + step) = site + shift site + difference := by dsimp only [difference]; abel
    have hz := hcompare _ _ ((hreach site).symm.trans hnext) hd heq
    simp only [direction, tilt, difference, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, Int.cast_add,
      Int.cast_sub] at hz ⊢
    linarith only [hz]
  · intro x y hxy
    have hsame' : representative x = representative y := hsame ⟨0, periods.zero_mem, by simpa only [add_zero] using hxy⟩
    have hy := hreach y
    rw [← hsame'] at hy
    have hlinked := (slide hxy (hspan x)).symm.trans ((hreach x).symm.trans hy)
    let difference := shift y - shift x
    have hd : difference ∈ deck.span := periods.sub_mem (hspan y) (hspan x)
    have heq : y + shift y = y + shift x + difference := by dsimp only [difference]; abel
    have hz := hcompare _ _ hlinked hd heq
    simp only [direction, tilt, difference, Prod.fst_sub, Prod.snd_sub, Int.cast_sub] at hz ⊢
    linarith only [hz]

/-- Every nonempty feasible quotient has a potential with two independent
tight windings. Otherwise their common annihilator would give a nonzero
perturbation preserving the extremizer's tight edges. -/
theorem exists_feasible_independent_tight_windings {deck : PeriodDeck} (hdet : 0 < deck.det) {k : ℤ} (hk : 2 ≤ k)
    (hphase : ∀ step ∈ deck.span, Retained k step) (negative positive : Field)
    (hneg : ∀ step ∈ deck.span, Function.Periodic negative step)
    (hpos : ∀ step ∈ deck.span, Function.Periodic positive step)
    (hne : (feasiblePotentialParameters hdet k negative positive).Nonempty) :
    ∃ param ∈ feasiblePotentialParameters hdet k negative positive, ∃ u ∈ deck.span, ∃ v ∈ deck.span,
      (u.1 * v.2 - u.2 * v.1 ≠ 0) ∧
      (∃ x, TightReaches k negative positive (evaluatePotential hdet param) x (x + u)) ∧
      ∃ y, TightReaches k negative positive (evaluatePotential hdet param) y (y + v) := by
  obtain ⟨param, hparam, hextreme⟩ := exists_feasible_extremum hdet hk hphase negative positive hneg hpos hne
  let potential := evaluatePotential hdet param
  let windings := tightWindings deck k negative positive potential
  refine ⟨param, hparam, ?_⟩
  by_contra hno
  have hdependent (u : Site) (hu : u ∈ windings) (v : Site) (hv : v ∈ windings) : u.1 * v.2 - u.2 * v.1 = 0 := by
    by_contra hdet'
    exact hno ⟨u, hu.1, v, hv.1, hdet', hu.2, hv.2⟩
  obtain ⟨a, b, hab, hzero⟩ := exists_annihilator_of_dependent windings hdependent
  obtain ⟨variation, hvar, hflat⟩ := exists_constant_on_tight_components (hasDeckSlope_evaluatePotential hdet param)
    hphase hneg hpos hzero
  obtain ⟨direction, ha, hb, hvalue⟩ := exists_evaluatePotential_of_deckSlope hdet hvar
  have hnormalized : evaluatePotential hdet direction 0 = 0 := by rw [hvalue, sub_self]
  have hzeroDirection : direction = 0 := hextreme direction hnormalized (fun site sign h => by
    have hedge : TightInput k negative positive potential site (inputAt k sign site) := by
      cases sign
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr ⟨rfl, h⟩
    have hreach : TightReaches k negative positive potential site (inputAt k sign site) := .single (Or.inl hedge)
    simp only [inputDifference, hvalue, hflat _ _ hreach, sub_self])
  rw [hzeroDirection] at ha hb
  exact hab.elim (fun h => h ha.symm) (fun h => h hb.symm)

end FLatticePaper.GeneralK
