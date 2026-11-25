import FLatticePaper.Plane.Induction.StripsM
import FLatticePaper.Plane.Induction.Q30White

/-! # The Q30 strip premises of a word, from the packet and the seed fields

For a word `word` with its conjugate's strong estimates `hSE`, the standard field `standardField word` has:

* `hstrip` (Q30's ordinary strip): `F = harmonicGrid` on the grades `[2 − 2d, 2L − 2]`, from the packet's harmonic strip
  (`ChildFrame.HasStrips`, `packet_of_strong`), weakened to Q30's range;
* `hodd` (Q30's odd extension): `F = harmonicGrid` on odd sites with grades in `[2 − 3d + n, 3d + n − 2]`. The grades split into three
  ranges. Below `1 − 2d`: the lower odd strip `hlowW_word`, from the price range, the price drifts and the odd seed line
  (`SeedFields.odd_bottom`). In `[1 − 2d, 2L − 1]`: the packet's harmonic strip. Above: the upper odd strip `odd_h0_upper`, by the
  reflection `ι` (`hIsym_word`) from the lower strip.

The word-level hypotheses are the ones of the standard word pipeline: `hw` (the word is not pure `3`-free), `hSE` (the conjugate's strong
estimates, which give the packet by `packet_of_strong`), `hbd` (the boundary price bound, the input of `priceRange_of_conjugate`), and
`hseed : SeedFields word` (for every word, `strongSeeds_of_all` supplies it). -/

namespace FLatticePaper.Q30Strips

open FLatticePaper FLatticePaper.Induction FLatticePaper.StripsM FLatticePaper.Q30White
open FLatticePaper.GameFort Farey

/-- **Q30's ordinary strip** of the standard field of a word, from the packet's harmonic strip. -/
theorem hstrip_of_strong {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    ∀ z : Site, 2 - 2 * (frameAt word).child.den ≤ (frameAt word).sGrade z →
      (frameAt word).sGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 2 →
      standardField word z = harmonicGrid z := by
  intro z h1 h2
  have hS := (packet_of_strong hw hSE).strips
  unfold ChildFrame.HasStrips at hS
  exact hS.2 z (by linarith) (by linarith)

/-- **Q30's odd extension** of the standard field of a word: the three ranges below, inside and above the packet's harmonic strip. -/
theorem hodd_of_strong {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hbd : ∀ z, OnBoundary (frameAt word).closedPolygon z →
      (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice)
    (hseed : W1Seeds.SeedFields word) :
    ∀ z : Site, ¬ EvenSite z →
      2 - 3 * (frameAt word).child.den + (frameAt word).child.num ≤ (frameAt word).sGrade z →
      (frameAt word).sGrade z ≤ 3 * (frameAt word).child.den + (frameAt word).child.num - 2 →
      standardField word z = harmonicGrid z := by
  intro z hz h1 h2
  have hlow := hlowW_word hw hSE hbd (fun w hw' hs => hseed.odd_bottom w hw' hs)
  by_cases hA : (frameAt word).sGrade z ≤ 1 - 2 * (frameAt word).child.den
  · exact hlow z hz h1 hA
  by_cases hB : (frameAt word).sGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1
  · have hS := (packet_of_strong hw hSE).strips
    unfold ChildFrame.HasStrips at hS
    exact hS.2 z (le_of_lt (not_le.mp hA)) hB
  · exact W1Strips.odd_h0_upper (frameAt word) (hIsym_word hw hSE) hlow z hz
      (le_of_lt (not_le.mp hB)) h2

/-- **`game_NW` for the standard field of a word.** The north middle's whiteness is discharged by Q30 from the word's strips. -/
theorem game_NW_of_strong {word : Word} (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    (hbd : ∀ z, OnBoundary (frameAt word).closedPolygon z →
      (frameAt word).price (standardField word) z ≤ (frameAt word).cutPrice)
    (hseed : W1Seeds.SeedFields word) {S : Set Site}
    (hG : IsGameFort (frameAt word) (-1) (standardField word) S)
    {z : Site} (hzS : z ∈ S) (hzV : z ∈ (frameAt word).freeV) (hzH : z ∉ (frameAt word).freeH) (ho : ¬ EvenSite z)
    (hzW : laplacian (standardField word) z = 0)
    (hS1 : 2 * (frameAt word).child.num + 2 - ((frameAt word).child.den - (frameAt word).child.num) ≤ (frameAt word).sGrade z)
    (hS2 : (frameAt word).sGrade z ≤ (frameAt word).child.den + (frameAt word).child.num - 2)
    (ht1 : (frameAt word).child.num + (frameAt word).child.den - 1 - (frameAt word).child.periodDenominator
      + (frameAt word).child.den < (frameAt word).tGrade z)
    (ht2 : (frameAt word).tGrade z < (frameAt word).child.den) :
    (z.1 - 1, z.2 + 1) ∈ S :=
  game_NW_of_strips (frameAt word) hG (hstrip_of_strong hw hSE) (hodd_of_strong hw hSE hbd hseed)
    hzS hzV hzH ho hzW hS1 hS2 ht1 ht2

end FLatticePaper.Q30Strips
