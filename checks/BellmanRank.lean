import FLatticePaper.Endpoint
import FLatticePaper.Plane.WeightedForts

open FLatticePaper FLatticePaper.Farey

private def deck : PeriodDeck := ⟨(1, -1), (0, 2)⟩

private theorem deck_covers : deck.Covers deck.residueSquare := by
  intro site
  have hdet : 0 < deck.det := by decide
  obtain ⟨representative, hmem, hcode⟩ := deck.exists_square_representative hdet site
  exact ⟨representative, hmem, (deck.classCode_eq_iff (ne_of_gt hdet) _ _).mp hcode⟩

private theorem deck_even (step : Site) (hmem : step ∈ deck.span) : EvenSite step := by
  obtain ⟨i, j, rfl⟩ := hmem
  simp only [EvenSite, deck, PeriodDeck.combine, mul_one, mul_zero, mul_neg, add_zero]
  omega

private theorem charge_add (step : Site) (hmem : step ∈ deck.span) (site : Site) :
    laplacian zeroEndpoint (site + step) = laplacian zeroEndpoint site := by
  simp only [laplacian_zeroEndpoint, evenSite_add_iff_of_even site step (deck_even step hmem)]

private theorem grade_add {step : Site} (hstep : EvenSite step) (site : Site) :
    checkerboardRank (site + step) = checkerboardRank site + 2 * step.1 := by
  simp only [EvenSite] at hstep
  simp only [checkerboardRank, Prod.fst_add, Prod.snd_add]
  omega

private def bulkOrder (site : Site) : ℕ := if EvenSite site then 0 else 1

private theorem no_bounded_fort (level : ℤ) (fort : Set Site) (hfort : fort.Nonempty)
    (hquota : IsIncomingFort zeroEndpoint fort) (hlevel : ∀ site ∈ fort, level ≤ checkerboardRank site) : False := by
  apply no_boundedFort_of_componentwise_exit (first := 0) (second := checkerboardRank) (free := EvenSite)
    (bulkOrder := bulkOrder) (freeOrder := fun _ => 0) (a := 1) (c := 1) 0 0 deck_even charge_add
    (fun _ _ => ⟨0, fun _ => by simp⟩) (fun step hmem => ⟨2 * step.1, grade_add (deck_even step hmem)⟩)
    ?_ ?_ ?_ (by decide) (by decide) level fort hfort hquota (by simpa using hlevel)
  · intro site hsite
    let step := deck.combine (-site.1) 0
    have hmem : step ∈ deck.span := ⟨-site.1, 0, rfl⟩
    refine ⟨step, hmem, (evenSite_add_iff_of_even site step (deck_even step hmem)).mpr hsite, rfl, ?_⟩
    rw [grade_add (deck_even step hmem)]
    change (site.1 + site.2) % 2 = 0 at hsite
    simp [checkerboardRank, hsite, step, deck, PeriodDeck.combine]
  · intro site hsite
    change ¬ EvenSite site at hsite
    have hneg : EvenSite (incomingNeg site) := by
      rw [incomingNeg, if_neg hsite]
      change (site.1 + (site.2 - 1)) % 2 = 0
      change (site.1 + site.2) % 2 ≠ 0 at hsite
      omega
    have hpos : EvenSite (incomingPos site) := by
      rw [incomingPos, if_neg hsite]
      change (site.1 + (site.2 + 1)) % 2 = 0
      change (site.1 + site.2) % 2 ≠ 0 at hsite
      omega
    rcases zeroEndpoint_rank site with ⟨hb, hn, hp⟩ | ⟨hw, _⟩
    · exact Or.inl ⟨hb, ⟨le_rfl, hn.le, by simp [bulkOrder, hsite, hneg]⟩,
        ⟨le_rfl, hp.le, by simp [bulkOrder, hsite, hpos]⟩⟩
    · have hblack : laplacian zeroEndpoint site = -1 := by simp [laplacian_zeroEndpoint, hsite]
      omega
  · intro fort hfort site hmem hsite _ hzero
    have hwhite : laplacian zeroEndpoint site = 0 := by simp [laplacian_zeroEndpoint, hsite]
    rcases hfort site hmem with ⟨hb, _⟩ | ⟨_, hneg, _⟩
    · omega
    · have hdrop : checkerboardRank (incomingNeg site) < checkerboardRank site := by
        simp only [checkerboardRank, incomingNeg, if_pos hsite]
        simp only [EvenSite] at hsite
        omega
      rw [hzero] at hdrop
      exact ⟨_, hneg, Or.inl ⟨le_rfl, hdrop.le, Or.inr hdrop⟩⟩

theorem zeroEndpoint_bellmanRank :
    ∃ (scale : ℤ) (remainder : Field), 0 < scale ∧ Recurrent zeroEndpoint ∧
      IsBurningRank zeroEndpoint (fun point => scale * checkerboardRank point + remainder point) := by
  have hgrade (step : Site) (hmem : step ∈ deck.span) :
      ∃ increment : ℤ, ∀ site, checkerboardRank (site + step) = checkerboardRank site + increment :=
    ⟨2 * step.1, grade_add (deck_even step hmem)⟩
  have hbinary (site : Site) : laplacian zeroEndpoint site = -1 ∨ laplacian zeroEndpoint site = 0 := by
    rw [laplacian_zeroEndpoint]
    split <;> simp
  obtain ⟨scale, remainder, _, hscale, _, _, hrank⟩ :=
    exists_burningRank_of_no_incomingFort deck_covers deck_even charge_add hgrade hbinary no_bounded_fort
  exact ⟨scale, remainder, hscale, hrank.recurrent, hrank⟩

#print axioms exists_burningRank_of_no_incomingFort
#print axioms no_boundedFort_of_componentwise_exit
#print axioms zeroEndpoint_bellmanRank
