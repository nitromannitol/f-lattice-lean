import FLatticePaper.Plane.Induction.HX2Diag

/-! # The chain form of hX1 and hX2 at the conjugate word

For a word `word`, the chain's `hX1` and `hX2` concern the child frame `frameAt (conjWord word)` and the standard field
`standardField (conjWord word)`. Its binary Laplacian is the packet of the word's own strong estimates `StrongEstimates (conjWord word)`
(the `hSE` of the chain, as in `HarmWrap`). The nonfree halves are the frame-level lemmas `ChildFrame.hX1_dichotomy` and
`ChildFrame.hX2_dichotomy`, which need no strips. -/

namespace FLatticePaper.Induction

open Farey

theorem hX1_of_strong {word : Word} (hSE : StrongEstimates (conjWord word)) {z : Site}
    (hz : z ∈ (frameAt (conjWord word)).freeV) (hev : EvenSite z) (hzF : z ≠ vFirst) {δ : ℤ}
    (hδ : δ = 1 ∨ δ = -1) (hδz : δ = 1 ∨ z ≠ (frameAt (conjWord word)).vLast) :
    laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = -1 ∨
      (laplacian (standardField (conjWord word)) (z.1 + δ, z.2) = 0 ∧
        Nonfree (frameAt (conjWord word)) (z.1 + δ, z.2)) :=
  (frameAt (conjWord word)).hX1_dichotomy (fun c => hSE.packet.binary c) hz hev hzF hδ hδz

theorem hX2_of_strong {word : Word} (hSE : StrongEstimates (conjWord word)) {z : Site}
    (hz : z ∈ (frameAt (conjWord word)).freeV) (hev : EvenSite z) (hzF : z ≠ vFirst) {δ : ℤ}
    (hδ : δ = 1 ∨ δ = -1) (hδz : δ = 1 ∨ z ≠ (frameAt (conjWord word)).vLast) :
    laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = -1 ∨
      (laplacian (standardField (conjWord word)) (z.1 + δ, z.2 - δ) = 0 ∧
        Nonfree (frameAt (conjWord word)) (z.1 + δ, z.2 - δ)) :=
  (frameAt (conjWord word)).hX2_dichotomy (fun c => hSE.packet.binary c) hz hev hzF hδ hδz

end FLatticePaper.Induction
