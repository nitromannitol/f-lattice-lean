import FLatticePaper.Construction.Placement

namespace FLatticePaper.Construction.HeightTile

private theorem insertAll_nonempty (first : HeightTile Site) (copies : List (HeightTile Site))
    (contacts : OrderedContacts first.sites copies) (hne : first.sites.Nonempty) :
    (first.insertAll copies contacts).sites.Nonempty :=
  hne.mono (first.subset_insertAll_sites copies contacts)

/-- After inserting the placed copies in the given order, trim the rectangular origin. -/
def meldPlaced (first : HeightTile Site) (copies : List (HeightTile Site))
    (contacts : OrderedContacts first.sites copies) (hne : first.sites.Nonempty) :
    HeightTile Site :=
  (first.insertAll copies contacts).trim (insertAll_nonempty first copies contacts hne)

/-- The finishing operations for a correction, in the constructor's order:
insert the placed copies, trim, then subtract the maximum. -/
def meldCorrection (first : HeightTile Site) (copies : List (HeightTile Site))
    (contacts : OrderedContacts first.sites copies) (hne : first.sites.Nonempty) :
    HeightTile Site :=
  (first.meldPlaced copies contacts hne).maxZero
    ((first.insertAll copies contacts).trim_sites_nonempty (insertAll_nonempty first copies contacts hne))

theorem meldPlaced_agrees (first : HeightTile Site) (copies : List (HeightTile Site))
    (contacts : OrderedContacts first.sites copies) (hne : first.sites.Nonempty)
    {target : Field} {gauge : ℤ} (hfirst : first.Agrees target gauge)
    (hcopies : OrderedComparisons target first.sites copies) :
    let raw := first.insertAll copies contacts
    (first.meldPlaced copies contacts hne).Agrees
      (fun site => target (site + raw.boxOrigin (insertAll_nonempty first copies contacts hne))) gauge :=
  (first.insertAll_agrees copies contacts hfirst hcopies).trim _

theorem meldCorrection_agrees (first : HeightTile Site) (copies : List (HeightTile Site))
    (contacts : OrderedContacts first.sites copies) (hne : first.sites.Nonempty)
    {target : Field} {gauge : ℤ} (hfirst : first.Agrees target gauge)
    (hcopies : OrderedComparisons target first.sites copies) :
    let raw := first.insertAll copies contacts
    ∃ correctionGauge, (first.meldCorrection copies contacts hne).Agrees
      (fun site => target (site + raw.boxOrigin (insertAll_nonempty first copies contacts hne)))
      correctionGauge :=
  ⟨_, (first.meldPlaced copies contacts hne).maxZero_agrees _
    (first.meldPlaced_agrees copies contacts hne hfirst hcopies)⟩

end FLatticePaper.Construction.HeightTile
