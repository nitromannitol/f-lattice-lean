import FLatticePaper.Tiles.TileStepAssembly
import FLatticePaper.Tiles.LatticeOfRespects

/-! # Item (c) of `lemma:weak_standard_odometer_properties` for the corrected standard tile odometers

The named input `TileStepAssembly.CorrectedLatticeInput` of the tile step, for the paper data. The tile part at `w` asks that the
standard tile odometers be defined on the standard tiles of `w` (the boundary tiles of the paper data) and respect their anchored
boundary strings, at every word, corrected or not. An odometer on a standard tile that respects its boundary strings is compatible
with its lattice adjacent translates (`LatticeOfRespects.latticeSelfCompatible_odd`, `latticeSelfCompatible_even`: the surrounding
of a standard tile consists of stacked zero-one boundary strings, `lemma:stacked_zero_one_string`). So (c) holds at the corrected
children too, along both lattice vectors. -/

namespace FLatticePaper.Tiles.CorrectedLatticePaper

open FLatticePaper.Tiles.JointFamily (JointData)
open FLatticePaper.Tiles.Standard (oddTile evenTile)

/-- **`CorrectedLatticeInput`** for the paper data: the L-corrected standard tile odometers at the corrected children (odd after a
`3`, even after a `2`) are lattice self-compatible along both lattice vectors of the child. -/
theorem correctedLattice_paper (D : JointData) (hS : D.S = WeakStepPaper.paperS) :
    TileStepAssembly.CorrectedLatticeInput D := by
  intro f w wo we wao wae tod tev aod aev _ hP
  obtain ⟨-, -, -, -, hRo, hRe, -, -, hdo, hde, -, -⟩ := hP
  have ho : tod.dom = oddTile w := by rw [hdo, hS]; rfl
  have he : tev.dom = evenTile w := by rw [hde, hS]; rfl
  rw [ho] at hRo
  rw [he] at hRe
  exact ⟨fun _ => LatticeOfRespects.latticeSelfCompatible_odd w tod ho hRo,
    fun _ => LatticeOfRespects.latticeSelfCompatible_even w tev he hRe⟩

end FLatticePaper.Tiles.CorrectedLatticePaper
