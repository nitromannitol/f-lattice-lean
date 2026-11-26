import FLatticePaper.Plane.Induction.PlusAdjacent
import FLatticePaper.Plane.Induction.W1HagreeNonfree
import FLatticePaper.Plane.Induction.FreePermitted

/-! # The adjacent chart of the forced permit, sign +1, at a nonnegative centre

For a forced edge `c → o` with `Ψ c ≥ 0` whose sheet pointer is `o`, and a strict target `Ψ o ≥ 1`, the sign +1 permit on the adjacent chart
(`c − uq`, `o − uq` in the polygon) follows from `PlusAdjacent.plus_adjacent_strictA`. The A-edge `c → o` comes from the sheet pointer
(`W1HagreeNonfree.sheetPolicyA_pointer_retained`). The tie target `Ψ o = 0` is not covered here. -/

namespace FLatticePaper.AdjacentPlus

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreePermitted

/-- **The adjacent sign +1 permit on an A-edge with a strict target.** -/
theorem permit_plus_adjacent_strict {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongCore word) (hSE : StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {c o : Site}
    (hc : c ∈ (frameAt word).closedPolygon) (ho : o ∈ (frameAt word).closedPolygon)
    (hcu : c - (frameAt word).uq ∈ (frameAt word).closedPolygon) (hou : o - (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : 0 ≤ FLatticePaper.W1Step.sheetPsi word c) (hΨo : 1 ≤ FLatticePaper.W1Step.sheetPsi word o)
    (hedge : sheetPolicyA P (frameAt word).sheetShift c o) :
    slipPermits (standardField word) (fun x => standardField word (x + (1 : ℤ) • (frameAt word).shortShift)) c o :=
  (slipPermits_iff_slip 1 c o).mpr
    (PlusAdjacent.plus_adjacent_strictA h hW hSE P hc ho hcu hou hΨc hΨo hedge)

/-- **The adjacent sign +1 permit from the sheet pointer.** If the forced input `o` of `c` is the sheet pointer (`sheetOut P c = o`) at a
nonnegative centre, the A-edge `c → o` holds, and the strict-target permit applies. -/
theorem permit_plus_adjacent_of_sheetOut {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hW : StrongCore word) (hSE : StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : FLatticePaper.W1Phase.OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed
      (frameAt word).eps)
    {c o : Site}
    (hc : c ∈ (frameAt word).closedPolygon) (ho : o ∈ (frameAt word).closedPolygon)
    (hcu : c - (frameAt word).uq ∈ (frameAt word).closedPolygon) (hou : o - (frameAt word).uq ∈ (frameAt word).closedPolygon)
    (hΨc : 0 ≤ FLatticePaper.W1Step.sheetPsi word c) (hΨo : 1 ≤ FLatticePaper.W1Step.sheetPsi word o)
    (hout : FLatticePaper.W1Step.sheetOut P (frameAt word).sheetShift (frameAt word).centre
      (FLatticePaper.W1Step.sheetPsi word) c = o) :
    slipPermits (standardField word) (fun x => standardField word (x + (1 : ℤ) • (frameAt word).shortShift)) c o := by
  have hret := W1HagreeNonfree.sheetPolicyA_pointer_retained P.toOldPolicyWitness.toOldPolicyData hSE.packet.binary
    (frameAt word).sheetShift (frameAt word).evenSite_sheetShift c
  unfold FLatticePaper.W1Step.sheetOut at hout
  rw [if_pos hΨc] at hout
  have hedge : sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift c o := by
    rw [← hout]
    exact hret
  exact permit_plus_adjacent_strict h hW hSE P.toOldPolicyWitness.toOldPolicyData hc ho hcu hou hΨc hΨo hedge

end FLatticePaper.AdjacentPlus
