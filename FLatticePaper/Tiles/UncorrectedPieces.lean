import FLatticePaper.Tiles.TileStepAssembly

/-! # The weak odometers at the uncorrected children respect the tile decompositions

`TileStepAssembly.UncorrectedPiecesInput`: at a child that is not corrected, the weak odometer of `w` respects the
decomposition of the tile odometer (`tOP`, `tEP`, `aOP`, `aEP`). These are the full decompositions that the weak parts carry at
the uncorrected children (`JointFamily.weakPart_full`, `JointFamily.weakAltPart_full`), over the family below `w`. It holds for
every joint data. -/

namespace FLatticePaper.Tiles.UncorrectedPieces

open FLatticePaper.Tiles.JointFamily (JointData)

/-- **`UncorrectedPiecesInput`**, for every joint data. -/
theorem uncorrectedPiecesInput (D : JointData) : TileStepAssembly.UncorrectedPiecesInput D := by
  intro f w wo we wao wae _ hw hWP hWA
  obtain ⟨h3, h2⟩ := JointFamily.weakPart_full hWP hw
  obtain ⟨a2, a3⟩ := JointFamily.weakAltPart_full hWA hw
  exact ⟨fun hc => ⟨h3 hc, a3 hc⟩, fun hc => ⟨h2 hc, a2 hc⟩⟩

end FLatticePaper.Tiles.UncorrectedPieces
