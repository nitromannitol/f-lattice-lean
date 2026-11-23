import FLatticePaper.Tiles.SiteStrings

/-! Task 53, item 4 (the lower-left vertex of the literal tiles): a normalised tile has lower-left vertex `(0, 0)`.

`IsNormalised T` says `0 ∈ T` and every `p ∈ T` satisfies `lexLE 0 p` (height first, then abscissa), which is the order used by
`lowLeft`. The literal standard tiles are normalised for every word (`standard_tiles_normalised`), so the marks of
`SourceHyps` are measured from the origin. -/

namespace FLatticePaper.Tiles.SiteLowLeft

open FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.SiteStrings

theorem lowLeft_of_normalised (T : Finset (ℤ × ℤ)) (h : IsNormalised T) : lowLeft T = (0, 0) := by
  obtain ⟨h0, hmin⟩ := h
  have hmem : toLex ((0 : ℤ × ℤ).2, (0 : ℤ × ℤ).1) ∈ T.image fun z => toLex (z.2, z.1) :=
    Finset.mem_image.mpr ⟨0, h0, rfl⟩
  have hge : ∀ b ∈ T.image fun z => toLex (z.2, z.1), toLex ((0 : ℤ × ℤ).2, (0 : ℤ × ℤ).1) ≤ b := by
    intro b hb
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hb
    have hp' := hmin p hp
    unfold lexLE at hp'
    rw [Prod.Lex.le_iff]
    rcases hp' with h1 | ⟨h1, h2⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, h2⟩
  have hmin' : (T.image fun z => toLex (z.2, z.1)).min = ↑(toLex ((0 : ℤ × ℤ).2, (0 : ℤ × ℤ).1)) :=
    le_antisymm (Finset.min_le hmem) (Finset.le_min fun b hb => WithTop.coe_le_coe.mpr (hge b hb))
  unfold lowLeft
  rw [hmin']
  rfl

theorem lowLeft_oddTile (w : FLatticePaper.Farey.Word) : lowLeft (oddTile w) = (0, 0) :=
  lowLeft_of_normalised _ (standard_tiles_normalised w).1

theorem lowLeft_evenTile (w : FLatticePaper.Farey.Word) : lowLeft (evenTile w) = (0, 0) :=
  lowLeft_of_normalised _ (standard_tiles_normalised w).2

end FLatticePaper.Tiles.SiteLowLeft
