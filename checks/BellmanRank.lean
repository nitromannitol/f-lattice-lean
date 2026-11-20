import FLatticePaper.Endpoint
import FLatticePaper.Plane.BellmanRank
import Mathlib.Data.Int.LeastGreatest

open FLatticePaper FLatticePaper.Farey

private def deck : PeriodDeck := ⟨(2, 0), (0, 2)⟩

private theorem deck_covers : deck.Covers deck.residueSquare := by
  intro site
  have hdet : 0 < deck.det := by decide
  obtain ⟨representative, hmem, hcode⟩ := deck.exists_square_representative hdet site
  exact ⟨representative, hmem, (deck.classCode_eq_iff (ne_of_gt hdet) _ _).mp hcode⟩

private theorem deck_even (step : Site) (hmem : step ∈ deck.span) : EvenSite step := by
  obtain ⟨i, j, rfl⟩ := hmem
  simp only [EvenSite, deck, PeriodDeck.combine, mul_zero, add_zero, zero_add]
  omega

private theorem no_bounded_fort (level : ℤ) (fort : Set Site) (hfort : fort.Nonempty)
    (hquota : IsIncomingFort zeroEndpoint fort) (hlevel : ∀ site ∈ fort, level ≤ checkerboardRank site) : False := by
  obtain ⟨first, hfirst⟩ := hfort
  obtain ⟨least, ⟨point, hpoint, hleast⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun value => ∃ site ∈ fort, checkerboardRank site = value)
    ⟨level, by rintro _ ⟨site, hsite, rfl⟩; exact hlevel site hsite⟩
    ⟨checkerboardRank first, first, hfirst, rfl⟩
  have houtside (input : Site) (hdrop : checkerboardRank input < checkerboardRank point) : input ∉ fort := by
    intro hin
    exact (not_lt_of_ge (hmin _ ⟨input, hin, rfl⟩)) (hleast ▸ hdrop)
  rcases zeroEndpoint_rank point with ⟨hb, hn, hp⟩ | ⟨hw, hn | hp⟩ <;>
    rcases hquota point hpoint with ⟨hblack, hin | hin⟩ | ⟨hwhite, hneg, hpos⟩
  · exact houtside _ hn hin
  · exact houtside _ hp hin
  · omega
  · omega
  · omega
  · exact houtside _ hn hneg
  · omega
  · omega
  · exact houtside _ hp hpos

theorem zeroEndpoint_bellmanRank :
    ∃ (scale : ℤ) (remainder : Field), 0 < scale ∧ Recurrent zeroEndpoint ∧
      IsBurningRank zeroEndpoint (fun point => scale * checkerboardRank point + remainder point) := by
  have hcharge (step : Site) (hmem : step ∈ deck.span) (site : Site) :
      laplacian zeroEndpoint (site + step) = laplacian zeroEndpoint site := by
    simp only [laplacian_zeroEndpoint, evenSite_add_iff_of_even site step (deck_even step hmem)]
  have hgrade (step : Site) (hmem : step ∈ deck.span) :
      ∃ increment : ℤ, ∀ site, checkerboardRank (site + step) = checkerboardRank site + increment := by
    refine ⟨2 * step.1, fun site => ?_⟩
    have hstep := deck_even step hmem
    simp only [EvenSite] at hstep
    simp only [checkerboardRank, Prod.fst_add, Prod.snd_add]
    omega
  have hbinary (site : Site) : laplacian zeroEndpoint site = -1 ∨ laplacian zeroEndpoint site = 0 := by
    rw [laplacian_zeroEndpoint]
    split <;> simp
  obtain ⟨scale, remainder, _, hscale, _, _, hrank⟩ :=
    exists_burningRank_of_no_incomingFort deck_covers deck_even hcharge hgrade hbinary no_bounded_fort
  exact ⟨scale, remainder, hscale, hrank.recurrent, hrank⟩

#print axioms exists_burningRank_of_no_incomingFort
#print axioms zeroEndpoint_bellmanRank
