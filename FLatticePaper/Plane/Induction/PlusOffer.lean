import FLatticePaper.Plane.Induction.SheetCharts
import FLatticePaper.Plane.Induction.MatchedPolicy

/-! # The first positive offer is nondecreasing along the sheet-`A` edges (Q34, W3)

`ψ₊(y) = pJump(y) = Fp(y − ε U_q) − Fp(y)` is the positive adjacent offer (`MatchedPolicy.pJump`). By `jumpA_eq_pJump` and
`jumpA_eq_cutPrice` it equals `c'₀ − P'(zTurn y)`, where `P'` is the conjugate's price. The conjugate's price is nonincreasing along
the retained edges of the policy (`OldPolicyData.priceNonincreasing`, through `parentPolicy_price`), and a sheet-`A` edge is a parent
edge (`sheetPolicyA` is `parentPolicy` at the shifted points). So `ψ₊` is nondecreasing along the sheet-`A` edges. -/

namespace FLatticePaper.PlusOffer

open Farey FLatticePaper FLatticePaper.Induction

/-- **The positive offer is the conjugate's price** (`ψ₊(y) = c'₀ − P'(zTurn y)`). -/
theorem pJump_eq_cutPrice {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (y : Site) :
    pJump (frameAt word) (quarterTurnField (standardField (conjWord word))) y =
      (frameAt (conjWord word)).cutPrice - (frameAt (conjWord word)).price (standardField (conjWord word)) (zTurn y) := by
  have h1 := jumpA_eq_pJump hSE ((1, -1) - y)
  rw [sub_sub_cancel] at h1
  have h2 := jumpA_eq_cutPrice h hSE ((1, -1) - y)
  rw [sub_sub_cancel] at h2
  rw [← h1]
  exact h2

/-- **The first positive offer is nondecreasing along a sheet-`A` edge.** The edge `sheetPolicyA P lv z u` is the parent edge
`parentPolicy P (z − lv) (u − lv)`, and the conjugate's price is nonincreasing along parent edges. -/
theorem pJump_mono_sheetA {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word))
    {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {z u : Site} (hedge : sheetPolicyA P (frameAt word).sheetShift z u) :
    pJump (frameAt word) (quarterTurnField (standardField (conjWord word))) (z - (frameAt word).sheetShift) ≤
      pJump (frameAt word) (quarterTurnField (standardField (conjWord word))) (u - (frameAt word).sheetShift) := by
  rw [pJump_eq_cutPrice h hSE, pJump_eq_cutPrice h hSE]
  have hm := parentPolicy_price P _ _ hedge
  exact hm

end FLatticePaper.PlusOffer
