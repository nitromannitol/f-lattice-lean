import FLatticePaper.Plane.Induction.AndOrRank
import FLatticePaper.Plane.RestrictedNoFortCriterion

/-! Task 72 (Q1 paragraphs 7 and 8): the uniform escape horizon.

Q1.md l.32: for each site the removal depth is finite (the restricted no-fort condition, `restrictedNoFort_iff_escape`, gives a finite
escape depth from the site's own grade level); deck covariance (`restrictedEscapesWithin_add`) makes the depth periodic, so over a
finite cover of the deck there is one maximum horizon `m` for all sites. That horizon is the `hescape` hypothesis of
`andOr_rank_of_escape`.

The stopping bound `t + m K(z_t) ≤ m K(z_0) + m + m² d_0` of Q1 is the value bound `restrictedValue_le_of_uniform_escape`
(`horizon · K + (horizon + horizon² · bound)`, with `bound = d_0`), already formal in `RestrictedBellmanRank`. -/

namespace FLatticePaper.AndOrRank

open Farey FLatticePaper

/-- **The uniform escape horizon.** Under the restricted no-fort condition, a finite cover of the deck, and the deck covariance of the
escape game, there is one horizon `m ≥ 1` from which every site escapes from its own grade level. -/
theorem uniform_escape_horizon {field grade : Field} {permits : Site → Site → Prop} {deck : PeriodDeck}
    {sites : Finset Site}
    (hno : RestrictedNoFort field grade permits) (hcover : deck.Covers sites)
    (hbinary : ∀ site, laplacian field site = -1 ∨ laplacian field site = 0)
    (heven : ∀ step ∈ deck.span, EvenSite step)
    (hcharge : ∀ step ∈ deck.span, ∀ site, laplacian field (site + step) = laplacian field site)
    (hgrade : ∀ step ∈ deck.span, ∃ inc : ℤ, ∀ site, grade (site + step) = grade site + inc)
    (hperm : ∀ step ∈ deck.span, ∀ site input, permits (site + step) (input + step) ↔ permits site input) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ site, RestrictedEscapesWithin field grade permits (grade site) m site := by
  have hsites := (restrictedNoFort_iff_cover hcover hbinary heven hcharge hgrade hperm).mp hno
  choose! N hN using hsites
  refine ⟨max 1 (sites.sup N), le_max_left _ _, fun site => ?_⟩
  obtain ⟨s, hs, hd⟩ := hcover site
  obtain ⟨inc, hinc⟩ := hgrade (site - s) hd
  have e : grade site = grade s + inc := by
    have h := hinc s
    rwa [show s + (site - s) = site by abel] at h
  have key := (restrictedEscapesWithin_add (heven _ hd) (hcharge _ hd) hinc (hperm _ hd) (grade s) (N s) s).mpr
    (hN s hs)
  rw [show s + (site - s) = site by abel, ← e] at key
  exact restrictedEscapesWithin_mono (le_trans (Finset.le_sup hs) (le_max_right _ _)) key

/-- **The rank under the restricted no-fort condition (paragraph 7 with the uniform horizon).** The horizon of
`andOr_rank_of_escape` is the one of `uniform_escape_horizon`, so the restricted no-fort condition alone gives the fixed point of the
Bellman iteration, read as a strict rank. -/
theorem andOr_rank_of_restrictedNoFort {field grade : Field} {permits : Site → Site → Prop} {deck : PeriodDeck}
    {sites : Finset Site} {bound : ℤ}
    (hno : RestrictedNoFort field grade permits) (hcover : deck.Covers sites)
    (hbinary : ∀ site, laplacian field site = -1 ∨ laplacian field site = 0)
    (heven : ∀ step ∈ deck.span, EvenSite step)
    (hcharge : ∀ step ∈ deck.span, ∀ site, laplacian field (site + step) = laplacian field site)
    (hgrade : ∀ step ∈ deck.span, ∃ inc : ℤ, ∀ site, grade (site + step) = grade site + inc)
    (hperm : ∀ step ∈ deck.span, ∀ site input, permits (site + step) (input + step) ↔ permits site input)
    (hloc : PermitLocal field permits)
    (hjump : ∀ site, grade (incomingNeg site) ≤ grade site + bound ∧ grade (incomingPos site) ≤ grade site + bound)
    (hbound : 0 ≤ bound) :
    ∃ m : ℕ, ∃ R : Field, (∀ site, R site = max ((m : ℤ) * grade site) (1 + restrictedInputs field permits R site)) ∧
      (∀ site, laplacian field site = -1 → ∀ i, (i = incomingNeg site ∨ i = incomingPos site) → R i + 1 ≤ R site) ∧
      (∀ site, laplacian field site = 0 →
        ∃ i, (i = incomingNeg site ∨ i = incomingPos site) ∧ permits site i ∧ R i + 1 ≤ R site) := by
  obtain ⟨m, _, hm⟩ := uniform_escape_horizon hno hcover hbinary heven hcharge hgrade hperm
  obtain ⟨R, hR⟩ := andOr_rank_of_escape hcover heven hcharge hgrade hperm hloc hjump hbound hm
  exact ⟨m, R, hR⟩

end FLatticePaper.AndOrRank
