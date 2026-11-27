import FLatticePaper.Plane.Induction.WordWebHyp
import FLatticePaper.Plane.Induction.WordVPattern
import FLatticePaper.Plane.Induction.W1StepParts

/-! # The H-block hypotheses at a word

For a word with its strong core `hS : StrongCore word` and its seed fields `hpar : SeedFields word`, the hypotheses of the H-block
and row lemmas hold at the frame `frameAt word` and the field `standardField word`:
* `hsig` is the slip sign bound (`W1StepParts.hsig_of_SE` with the slip range of the core);
* `hZ3` is the extended even zero window `[2 − L, 2L − 2]` (`webHyp_word`, which is `W1Strips.even_zero_full`);
* `hZ2` is the sub-window `[n + 2d − 1, 2L − 2]` of the same zero window;
* `hrL2` is `brk word ≤ L − 2` (`WordVPattern.brk_add_two_le`). -/

namespace FLatticePaper.WordDischarge

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Seeds FLatticePaper.WordWebHyp FLatticePaper.WordVPattern

/-- **hsig at the word.** -/
theorem hsig_word {word : Word} (hS : StrongCore word) :
    ∀ w ∈ (frameAt word).closedPolygon,
      standardField word w - standardField word (w - (frameAt word).shortShift) ≤ 0 :=
  FLatticePaper.W1StepParts.hsig_of_SE hS.packet (fun z hz => hS.slipRange z hz)

/-- **hZ3 at the word:** the even zeros on the window `2 − L ≤ t ≤ 2L − 2`. -/
theorem hZ3_word {word : Word} (hS : StrongCore word) (hpar : SeedFields word) :
    ∀ w : Site, EvenSite w → 2 - ((frameAt word).child.den + (frameAt word).child.num) ≤ (frameAt word).tGrade w →
      (frameAt word).tGrade w ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 2 →
      standardField word w = 0 :=
  fun w hw hlo hhi => (webHyp_word hS hpar).evenExt w hw hlo hhi

/-- **hZ2 at the word:** the even zeros on the window `n + 2d − 1 ≤ t ≤ 2L − 2`, a sub-window of `hZ3_word`. -/
theorem hZ2_word {word : Word} (hS : StrongCore word) (hpar : SeedFields word) :
    ∀ w : Site, EvenSite w → (frameAt word).child.num + 2 * (frameAt word).child.den - 1 ≤ (frameAt word).tGrade w →
      (frameAt word).tGrade w ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 2 →
      standardField word w = 0 := by
  intro w hw hlo hhi
  obtain ⟨hn0, hnd, -, -, -⟩ := (frameAt word).child_facts
  exact hZ3_word hS hpar w hw (by omega) hhi

/-- **hrL2 at the word:** the minus break `r = brk word` satisfies `r ≤ L − 2`. -/
theorem hrL2_word (word : Word) :
    brk word ≤ (frameAt word).child.den + (frameAt word).child.num - 2 := by
  have h := brk_add_two_le word
  linarith

end FLatticePaper.WordDischarge
