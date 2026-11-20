import FLatticePaper.Plane.QuarterTurn
import FLatticePaper.Plane.Recurrence

namespace FLatticePaper

theorem QuarterTurn.incomingDegree_map (direction : QuarterTurn) (offset : Site)
    (hoffset : ¬ EvenSite offset) (sites : Finset Site) (site : Site) :
    incomingDegree (sites.map (direction.siteEquiv offset).toEmbedding)
      (direction.mapSite offset site) = incomingDegree sites site := by
  have hmem (point : Site) :
      direction.mapSite offset point ∈ sites.map (direction.siteEquiv offset).toEmbedding ↔
        point ∈ sites :=
    Finset.mem_map' (direction.siteEquiv offset).toEmbedding
  unfold incomingDegree
  rcases direction.incoming_star offset site hoffset with ⟨hn, hp⟩ | ⟨hn, hp⟩
  · simp only [hn, hp, hmem]
  · simp only [hn, hp, hmem]
    exact Int.add_comm ..

/-- Recurrence invariance for superharmonic fields, without any assumption
that a decreasing rank has been constructed for the original field. -/
theorem Recurrent.quarterTurn {field correction : Field}
    (hrec : Recurrent field) (hsuper : Superharmonic field) (direction : QuarterTurn)
    (offset : Site) (hoffset : ¬ EvenSite offset) (hcorrection : Harmonic correction) :
    let rotated : Field := fun site => field (direction.mapSite offset site) + correction site
    Superharmonic rotated ∧ Recurrent rotated := by
  dsimp only
  constructor
  · intro site
    rw [laplacian_quarterTurn_add_harmonic direction offset hoffset field correction hcorrection]
    exact hsuper _
  · apply recurrent_of_allowed
    intro sites hne
    let embedding := (direction.siteEquiv offset).toEmbedding
    obtain ⟨imageSite, himageSite, hallowed⟩ :=
      hrec.allowed hsuper (sites.map embedding) hne.map
    obtain ⟨site, hsite, rfl⟩ := Finset.mem_map.mp himageSite
    refine ⟨site, hsite, ?_⟩
    dsimp only
    rw [laplacian_quarterTurn_add_harmonic direction offset hoffset field correction hcorrection]
    rw [← direction.incomingDegree_map offset hoffset sites site]
    exact hallowed

end FLatticePaper
