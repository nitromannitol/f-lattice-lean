import FLatticePaper.Plane.Induction.PassagePR
import FLatticePaper.Plane.Induction.TransferW1
import FLatticePaper.Plane.Induction.ForcedPriceSI

/-! # The rounded monotonicity of a forced edge at a strict-interior white (`RoundedMonoForced`, local form)

`W4Reduction.RoundedMonoForced word` is a statement for every white forced edge in the polygon. The comparison argument behind it
(`ComparisonEmpty.jminus_nonincrease_forced_of_sat`) needs the hypothesis `hT`, which says that at a contact the forced input of a comparison
field is not below the field. That hypothesis is `TransferW1.hT_strict` at strict-interior contacts. Here we combine the two, with
`HasSatSelection` (the Q1 rank) and `priceRangeOn_of_strong` (from `StrongCore`), to prove the rounded inequality at every strict-interior
white forced edge of the polygon. -/

namespace FLatticePaper.RoundedLocal

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses

/-- **The rounded monotonicity at strict-interior forced whites.** The conclusion is the inequality of `RoundedMonoForced` for the edge
`c → o`, with `c` strictly interior. The premises are the Q1 satisfiability `hW`, the W1 forcing `hW1` of the word, and the strong data. -/
theorem rounded_forced_SI {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hWord : StrongCore word) (hSE : StrongEstimates (conjWord word))
    (hW : HasSatSelection (standardField word))
    (hW1 : FLatticePaper.W1.W1Forced (frameAt word).child.num (frameAt word).child.den (standardField word))
    {c o : Site}
    (hSIc : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hw : laplacian (standardField word) c = 0) (hcE : c ∈ (frameAt word).closedPolygon)
    (hf : ForcedEdge (standardField word) (fun _ _ => False) c o) (hoE : o ∈ (frameAt word).closedPolygon) :
    (standardField word o - standardField word (o + -(frameAt word).shortShift) + 1) / 2 ≤
      (standardField word c - standardField word (c + -(frameAt word).shortShift) + 1) / 2 := by
  have hPR := ForcedPriceSI.priceRangeOn_of_strong hWord
  refine PassagePR.jminus_nonincrease_forced_of_sat_PR h hSE hPR hW ?_ hSIc hw hcE hf hoE
  intro m hm c' o' hSI hw' hc' hf' _ hlt
  exact absurd (TransferW1.hT_strict h hSE hPR hW hW1 hm hSI hw' hc' hf') (ne_of_gt hlt)

end FLatticePaper.RoundedLocal
