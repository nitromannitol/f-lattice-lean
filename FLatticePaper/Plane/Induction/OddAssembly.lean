import FLatticePaper.Plane.Induction.TieOpt2
import FLatticePaper.Plane.Induction.OddRise

/-! Task 69 (c): `OddBlackNoRise` from `NoBlackPairRise` (`oddBlackNoRise_standard`), with `NoBlackPairRise` assembled from
the conjugate's strong estimates and the old policy (`noBlackPairRise_of_leaves`). The named leaves are the word's slip
range `hslip`, the word's unit slip `hU` (the `F1_unitSlip` field of the word's slip fields), and the tie leaf `hTie`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper

theorem oddBlackNoRise_of_leaves {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hpk : (frameAt word).Packet (standardField word))
    {seed : Site → Site → Prop} (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (hslip : ∀ z ∈ (frameAt word).closedPolygon,
      0 ≤ standardField word z - standardField word (z + (frameAt word).shortShift) ∧
        standardField word z - standardField word (z + (frameAt word).shortShift) ≤ 2)
    (hU : HasUnitSlip (standardField word) (fun z => standardField word (z + (frameAt word).shortShift)))
    (hTie : ∀ c i, RisingBlackPair (standardField word) (frameAt word).shortShift c i →
      c ∈ (frameAt word).closedPolygon → (sheetDiffW word c = 0 ∨ sheetDiffW word i = 0) → False) :
    OddBlackNoRise (standardField word) (frameAt word).shortShift :=
  oddBlackNoRise_standard word hpk hU (noBlackPairRise_of_leaves h hSE hpk P hslip hTie)

end FLatticePaper.Induction
