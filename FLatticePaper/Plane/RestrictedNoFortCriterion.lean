import FLatticePaper.Plane.RestrictedBellmanRank
import FLatticePaper.Plane.AlternateSlip

/-! A criterion for the restricted no-fort condition (task 28).

`RestrictedNoFort` quantifies over every nonempty restricted fort in every grade half-space. Two facts reduce it to finitely
many escape statements:

* a restricted fort never escapes: for a fort in `{grade ≥ level}` and any site of the fort, no restricted escape from
  `level` exists at any depth (`not_restrictedEscapesWithin_of_fort`);
* conversely, a fort contains a site of least grade, and that site does not escape at its own level.

Hence `RestrictedNoFort` is equivalent to: every site escapes from its own grade level at some finite depth
(`restrictedNoFort_iff_escape`). Escape is equivariant under the deck (an even translation shifts the level by the grade
increment), so it suffices to check a cover of the deck (`restrictedNoFort_iff_cover`). -/

namespace FLatticePaper

open Farey

/-- A restricted fort in `{grade ≥ level}` contains no site that escapes from `level` at any depth. -/
theorem not_restrictedEscapesWithin_of_fort {field grade : Field} {permits : Site → Site → Prop} {level : ℤ}
    {fort : Set Site} (hfort : IsRestrictedFort field permits fort) (hlev : ∀ site ∈ fort, level ≤ grade site) :
    ∀ (n : ℕ) (site : Site), site ∈ fort → ¬ RestrictedEscapesWithin field grade permits level n site := by
  intro n
  induction n with
  | zero =>
    intro site hsite hesc
    have h := hlev site hsite
    simp only [RestrictedEscapesWithin] at hesc
    omega
  | succ n ih =>
    intro site hsite hesc
    have hl := hlev site hsite
    simp only [RestrictedEscapesWithin] at hesc
    rcases hesc with hlow | ⟨hlap, hpn, hpp, hen, hep⟩ | ⟨hlap, hopt⟩
    · omega
    · rcases hfort site hsite with ⟨-, hn | hp⟩ | ⟨hl0, -⟩
      · rcases hn with hin | hnp
        · exact ih _ hin hen
        · exact hnp hpn
      · rcases hp with hin | hnp
        · exact ih _ hin hep
        · exact hnp hpp
      · rw [hlap] at hl0
        norm_num at hl0
    · rcases hfort site hsite with ⟨hl1, -⟩ | ⟨-, hn, hp⟩
      · rw [hlap] at hl1
        norm_num at hl1
      · rcases hopt with ⟨hpn, hen⟩ | ⟨hpp, hep⟩
        · rcases hn with hin | hnp
          · exact ih _ hin hen
          · exact hnp hpn
        · rcases hp with hin | hnp
          · exact ih _ hin hep
          · exact hnp hpp

/-- The restricted no-fort condition is equivalent to escape from every site at its own grade level. -/
theorem restrictedNoFort_iff_escape {field grade : Field} {permits : Site → Site → Prop}
    (hbinary : ∀ site, laplacian field site = -1 ∨ laplacian field site = 0) :
    RestrictedNoFort field grade permits ↔
      ∀ site, ∃ n, RestrictedEscapesWithin field grade permits (grade site) n site := by
  classical
  constructor
  · intro hno site
    exact exists_restrictedEscapeDepth hbinary (fun sites hne hfort hlev => hno (grade site) sites hne hfort hlev) site
  · intro hall level fort hne hfort hlev
    obtain ⟨x, hx⟩ := hne
    obtain ⟨lb, hlb, hmin⟩ := Int.exists_least_of_bdd
      (P := fun z => ∃ y ∈ fort, grade y = z)
      ⟨level, fun z ⟨y, hy, hyz⟩ => hyz ▸ hlev y hy⟩ ⟨grade x, x, hx, rfl⟩
    obtain ⟨y, hy, hyg⟩ := hlb
    obtain ⟨n, hn⟩ := hall y
    have hlev' : ∀ z ∈ fort, grade y ≤ grade z := fun z hz => by
      rw [hyg]
      exact hmin (grade z) ⟨z, hz, rfl⟩
    exact not_restrictedEscapesWithin_of_fort hfort hlev' n y hy hn

/-- Escape is equivariant under an even deck step: translating a site by the step translates its escape with the level
shifted by the grade increment. -/
theorem restrictedEscapesWithin_add {field grade : Field} {permits : Site → Site → Prop} {step : Site} {inc : ℤ}
    (heven : EvenSite step) (hcharge : ∀ site, laplacian field (site + step) = laplacian field site)
    (hgrade : ∀ site, grade (site + step) = grade site + inc)
    (hperm : ∀ site input, permits (site + step) (input + step) ↔ permits site input) (level : ℤ) :
    ∀ (n : ℕ) (site : Site),
      RestrictedEscapesWithin field grade permits (level + inc) n (site + step) ↔
        RestrictedEscapesWithin field grade permits level n site := by
  intro n
  induction n with
  | zero =>
    intro site
    simp only [RestrictedEscapesWithin, hgrade, add_lt_add_iff_right]
  | succ n ih =>
    intro site
    simp only [RestrictedEscapesWithin, hcharge, hgrade, add_lt_add_iff_right,
      incomingNeg_add_of_even site step heven, incomingPos_add_of_even site step heven, hperm, ih]

/-- Finite-quotient criterion: given a cover of the deck by finitely many sites, the restricted no-fort condition holds
iff every cover site escapes from its own grade level. -/
theorem restrictedNoFort_iff_cover {field grade : Field} {permits : Site → Site → Prop}
    {deck : PeriodDeck} {sites : Finset Site}
    (hcover : deck.Covers sites)
    (hbinary : ∀ site, laplacian field site = -1 ∨ laplacian field site = 0)
    (heven : ∀ step ∈ deck.span, EvenSite step)
    (hcharge : ∀ step ∈ deck.span, ∀ site, laplacian field (site + step) = laplacian field site)
    (hgrade : ∀ step ∈ deck.span, ∃ inc : ℤ, ∀ site, grade (site + step) = grade site + inc)
    (hperm : ∀ step ∈ deck.span, ∀ site input, permits (site + step) (input + step) ↔ permits site input) :
    RestrictedNoFort field grade permits ↔
      ∀ site ∈ sites, ∃ n, RestrictedEscapesWithin field grade permits (grade site) n site := by
  rw [restrictedNoFort_iff_escape hbinary]
  constructor
  · intro h site _
    exact h site
  · intro h site
    obtain ⟨rep, hrep, hv⟩ := hcover site
    obtain ⟨n, hn⟩ := h rep hrep
    obtain ⟨step, hstep, hsite⟩ : ∃ step, step ∈ deck.span ∧ site = rep + step :=
      ⟨site - rep, hv, by abel⟩
    obtain ⟨inc, hinc⟩ := hgrade step hstep
    subst hsite
    refine ⟨n, ?_⟩
    rw [hinc rep]
    exact (restrictedEscapesWithin_add (heven step hstep) (hcharge step hstep) hinc (hperm step hstep)
      (grade rep) n rep).2 hn

end FLatticePaper
