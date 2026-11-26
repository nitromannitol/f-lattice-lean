import FLatticePaper.Plane.Induction.ProtectedWeb
import FLatticePaper.Plane.Induction.OppWordCover
import FLatticePaper.Plane.Induction.W1StepParts
import FLatticePaper.Plane.Induction.W1Strips
import FLatticePaper.Plane.Induction.W1Seeds
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! # The protected web hypotheses at the word's own field (Q39, the word frame)

For a word `word` with `StrongCore word` (packet, slip range) and `SeedFields word` (even seed), the field `standardField word` on
the child frame `frameAt word` satisfies `ProtectedWeb.WebHyp`:
* `strips`, `inv`: the packet strips and the deck invariance of the Laplacian (`laplacian_add_combine`);
* `evenExt`: the extended even zero interval `[2 − L, 2L − 2]` (`W1Strips.even_zero_full`, with the reflection `iRefl_core` and the
  even seed `SeedFields.even_zero`);
* `oddExt`: the odd `h₀` band `[2 − 3d + n, 3d + n − 2]` by `OppWordCover.word_odd_lower`, `word_odd_upper` and the harmonic strip
  `word_strip` in the middle.
Then the free-input property `freeInput_eq` holds at the word. -/

namespace FLatticePaper.WordWebHyp

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.ProtectedWeb FLatticePaper.W1Seeds FLatticePaper.SquareClauses

theorem webHyp_word {word : Word} (hS : StrongCore word) (hpar : SeedFields word) :
    WebHyp (frameAt word) (standardField word) where
  strips := hS.packet.strips
  inv := fun z v hv => by
    obtain ⟨i, j, rfl⟩ := hv
    exact laplacian_add_combine hS.packet.periods z i j
  evenExt := fun z hz hlo hhi =>
    W1Strips.even_zero_full (frameAt word) (W1StepParts.hper_of_packet hS.packet) hS.packet.strips
      (fun y hy => (hS.slipRange y hy).1) hpar.even_zero (fun y => W1Strips.standardField_iRefl_core hS y) z hz hlo hhi
  oddExt := fun z hz hlo hhi => by
    obtain ⟨hn0, -, -, hd3, -⟩ := (frameAt word).child_facts
    rcases le_or_gt ((frameAt word).sGrade z) (1 - 2 * (frameAt word).child.den) with h1 | h1
    · exact OppWordCover.word_odd_lower hS hpar z hz hlo h1
    · rcases le_or_gt ((frameAt word).sGrade z) ((frameAt word).child.den + (frameAt word).child.num - 2) with h2 | h2
      · exact OppWordCover.word_strip hS z h1.le (by linarith)
      · exact OppWordCover.word_odd_upper hS hpar z hz h2 hhi

/-- **`hFreeIn` at the word**: a forced white of `standardField word` whose input `o` is free forces `o`. -/
theorem hFreeIn_word {word : Word} (hS : StrongCore word) (hpar : SeedFields word) {c i o : Site}
    (h : ForcedEdge (standardField word) (fun _ _ => False) c i) (ho : o = incomingNeg c ∨ o = incomingPos c)
    (hfo : o ∈ (frameAt word).freeH ∨ o ∈ (frameAt word).freeV) : o = i :=
  freeInput_eq (webHyp_word hS hpar) h ho hfo

end FLatticePaper.WordWebHyp
