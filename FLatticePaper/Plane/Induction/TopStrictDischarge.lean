import FLatticePaper.Plane.Induction.CollarChain
import FLatticePaper.Plane.Induction.TopSquare
import FLatticePaper.Plane.Induction.ColourPacket

/-! # The discharge of `TopStrictHyp` from the packet (after `CollarChain`)

`TopStrictHyp word G lvAt` is the named input of the collar chain. Its conclusion is the word-image strictness proved in
`TopSquare.top_corner_strict`; the strips of the word's sheet minimum come from `StripsM.stripInputs_M` (the
`StrongEstimates` of the conjugate word) by `ChildFrame.hasStrips_of_stripInputs`. The one periodicity premise
`HasGeneratorPeriods (frameAt word).child (MW word)` at the frame's own constants is a named argument here. -/

namespace FLatticePaper.TopStrictDischarge

open FLatticePaper FLatticePaper.W1 FLatticePaper.W1OffCollar FLatticePaper.W1Phase FLatticePaper.Induction
  FLatticePaper.CollarChain FLatticePaper.W1MSheet FLatticePaper.Farey

/-- The top-square strictness hypothesis of the collar chain, from the conjugate packet alone. The colour facts it uses
are the standard field's, transferred to the sheet minimum at their stencils (`ColourPacket`). -/
theorem topStrictHyp_of_packet {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    TopStrictHyp word (standardField (conjWord word)) (frameAt word).sheetShift := by
  intro c v ρ o a b inside hc hM _ hWit hρ hv _ hsq hρS _ _ _ _ _
  exact TopSquare.top_corner_strict word hw hSE c v ρ a b hc hM hWit hρ hv hsq hρS

end FLatticePaper.TopStrictDischarge
