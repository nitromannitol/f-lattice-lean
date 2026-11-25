import FLatticePaper.Plane.Induction.W4Reduction
import FLatticePaper.Plane.Induction.RawB

/-! # W4 (Q35): the negative-chart offer is the conjugate's raw slip

`BOffer word z = C(z + uq) − A z` (W4Reduction) equals `(1 + ε) − D'_ε(Z x)` at `x = z − sheetShift`, with `D'_ε = slip ε` of the
conjugate frame (`RawB.sheetB_eq`, from `paragraph6_of_strong`). Since `1 + ε = 2W`, this is Q35's `B(x) = 2W − D'_ε(Zx)`. -/

namespace FLatticePaper.W4OfferB

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W4Reduction

/-- **The offer as the raw slip.** `BOffer word z = (1 + ε) − D'_ε(Z(z − sheetShift))`, with `D'_ε = (frameAt (conjWord word)).slip`. -/
theorem BOffer_eq_one_add_eps_sub_slip {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (z : Site) :
    BOffer word z = (1 + (frameAt word).eps) -
      (frameAt (conjWord word)).slip (standardField (conjWord word)) (frameAt word).eps
        (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1) := by
  unfold BOffer ChildFrame.slip
  exact sheetB_eq h hSE z

end FLatticePaper.W4OfferB
