import FLatticePaper.Tiles.JointRot
import FLatticePaper.Tiles.WeakStepAssembly

/-! # The zero-slope normalisation of the tile odometers for the paper data

The named input `WeakStepAssembly.TileSlopeZero` of the weak step: every tile odometer of a good family is normalised on its first
tile with zero slope. This is `JointRot.family_slopes` (induction over the words, from the base cases `JointRot.baseSlopes_paper`
and the decompositions of `TilePart`), applied at the length of the word. -/

namespace FLatticePaper.Tiles.TileSlopeZeroPaper

open FLatticePaper.Tiles.JointFamily (JointData)

/-- **`TileSlopeZero`** for the paper data. -/
theorem tileSlopeZero_paper (D : JointData) (hS : D.S = WeakStepPaper.paperS)
    (hA : D.altBase = SurgicalAlt.PaperAltBaseCond) : WeakStepAssembly.TileSlopeZero D := by
  intro f n hgood u hu
  obtain ⟨h1, h2, -, -⟩ := JointRot.family_slopes D f u.length
    (fun v hv => (hgood v (lt_of_le_of_lt hv hu)).1) (JointRot.baseSlopes_paper D hS hA) u le_rfl
  exact ⟨h1, h2⟩

end FLatticePaper.Tiles.TileSlopeZeroPaper
