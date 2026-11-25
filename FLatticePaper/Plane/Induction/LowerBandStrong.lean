import FLatticePaper.Plane.Induction.LowerBand
import FLatticePaper.Plane.Induction.Q30Strips

/-! # The lap-0 half of `hX3` at the conjugate word, from the strong estimates

For a word `word`, the chain's `hX3` concerns the child frame `frameAt (conjWord word)` and its standard field
`standardField (conjWord word)`. Its harmonic strip is `Q30Strips.hstrip_of_strong` at the word `conjWord word`, which needs
the strong estimates of `conjWord (conjWord word)` (the `hSE'` of `TraceStep`) and the word's non-pure-three witness
`hw : ∃ x ∈ conjWord word, x ≠ three`. Then `LowerBand.lap_lower_eq_zero` gives the Laplacian of the lower input. -/

namespace FLatticePaper.Induction

open Farey

/-- A word that is not a power of `3` has a digit other than `3`. -/
theorem exists_ne_three_of_not_replicate (w : Word) (h : ¬ ∃ k : ℕ, w = List.replicate k Digit.three) :
    ∃ x ∈ w, x ≠ Digit.three := by
  by_contra hc
  apply h
  refine ⟨w.length, List.eq_replicate_iff.mpr ⟨rfl, fun b hb => ?_⟩⟩
  by_contra hne
  exact hc ⟨b, hb, hne⟩

/-- The lap-0 half of `hX3` at the conjugate word, for a word whose conjugate is not a power of `3` (the chain's hypothesis
`¬ ∃ k, conjWord word = replicate k three`). -/
theorem lap_lower_of_strong {word : Word} (hnot : ¬ ∃ k : ℕ, conjWord word = List.replicate k Digit.three)
    (hSE : StrongEstimates (conjWord (conjWord word))) {z : Site}
    (hz : z ∈ (frameAt (conjWord word)).freeV) (hev : EvenSite z) (hzF : z ≠ vFirst) {δ : ℤ}
    (hδ : δ = 1 ∨ δ = -1) (hδz : δ = 1 ∨ z ≠ (frameAt (conjWord word)).vLast) :
    laplacian (standardField (conjWord word)) (z.1, z.2 - δ) = 0 :=
  (frameAt (conjWord word)).lap_lower_eq_zero
    (FLatticePaper.Q30Strips.hstrip_of_strong (exists_ne_three_of_not_replicate _ hnot) hSE) hz hev hzF hδ hδz

end FLatticePaper.Induction
