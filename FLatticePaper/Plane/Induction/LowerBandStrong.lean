import FLatticePaper.Plane.Induction.LowerBand
import FLatticePaper.Plane.Induction.Q30Strips

/-! # The lap-0 half of `hX3` at the conjugate word, from the strong estimates

For a word `word`, the chain's `hX3` concerns the child frame `frameAt (conjWord word)` and its standard field
`standardField (conjWord word)`. Its harmonic strip is `Q30Strips.hstrip_of_strong` at the word `conjWord word`, which needs
the strong estimates of `conjWord (conjWord word)` (the `hSE'` of `TraceStep`) and the word's non-pure-three witness
`hw : ∃ x ∈ conjWord word, x ≠ three`. Then `LowerBand.lap_lower_eq_zero` gives the Laplacian of the lower input. -/

namespace FLatticePaper.Induction

open Farey

theorem lap_lower_of_strong {word : Word} (hw : ∃ x ∈ conjWord word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord (conjWord word))) {z : Site}
    (hz : z ∈ (frameAt (conjWord word)).freeV) (hev : EvenSite z) (hzF : z ≠ vFirst) {δ : ℤ}
    (hδ : δ = 1 ∨ δ = -1) (hδz : δ = 1 ∨ z ≠ (frameAt (conjWord word)).vLast) :
    laplacian (standardField (conjWord word)) (z.1, z.2 - δ) = 0 :=
  (frameAt (conjWord word)).lap_lower_eq_zero (FLatticePaper.Q30Strips.hstrip_of_strong hw hSE) hz hev hzF hδ hδz

end FLatticePaper.Induction
