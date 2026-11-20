import FLatticePaper.Construction.OrderedOverlap

namespace FLatticePaper.Construction.HeightTile

variable {α : Type*} [DecidableEq α]

/-- The height operation for a correction: insert all the already placed copies
in order, then subtract the maximum. The list supplies the spatial placements. -/
def correctionHeight (first : HeightTile α) (copies : List (HeightTile α))
    (contacts : OrderedContacts first.sites copies) (hne : first.sites.Nonempty) : HeightTile α :=
  (first.insertAll copies contacts).maxZero (hne.mono (first.subset_insertAll_sites copies contacts))

/-- Normalizing the correction changes only its single height constant. -/
theorem correctionHeight_agrees (first : HeightTile α) (copies : List (HeightTile α))
    (contacts : OrderedContacts first.sites copies) (hne : first.sites.Nonempty)
    {target : α → ℤ} {gauge : ℤ} (hfirst : first.Agrees target gauge)
    (hcopies : OrderedComparisons target first.sites copies) :
    ∃ correctionGauge, (first.correctionHeight copies contacts hne).Agrees target correctionGauge :=
  ⟨_, (first.insertAll copies contacts).maxZero_agrees _
    (first.insertAll_agrees copies contacts hfirst hcopies)⟩

/-- If the placed correction and the outer prefix are priced by the same
target, outer insertion absorbs the correction's internal maximum normalization. -/
theorem insert_correctionHeight_agrees (old first : HeightTile α) (copies : List (HeightTile α))
    (contacts : OrderedContacts first.sites copies) (hne : first.sites.Nonempty)
    (contact : (old.sites ∩ (first.correctionHeight copies contacts hne).sites).Nonempty)
    {target : α → ℤ} {oldGauge firstGauge : ℤ} (hold : old.Agrees target oldGauge)
    (hfirst : first.Agrees target firstGauge)
    (hcopies : OrderedComparisons target first.sites copies) :
    (old.insert (first.correctionHeight copies contacts hne) contact).Agrees target oldGauge := by
  obtain ⟨_, hcorrection⟩ := first.correctionHeight_agrees copies contacts hne hfirst hcopies
  exact old.insert_agrees _ contact hold (hcorrection.fits contact)

end FLatticePaper.Construction.HeightTile
