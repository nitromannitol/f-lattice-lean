import FLatticePaper.Plane.Induction.SheetStars
import FLatticePaper.Plane.Induction.Sec3Monotone

/-! The §3 permit for free V whites `w ≠ V_end`: `D₊(u) ≤ D₊(w)` for the prescribed input `u = w + prescribedV 1 w`.
The h0 equalities and the shifted stars are proved (`FreeVH0`, `SheetStars`). The native retention of the edge
`zTurn(w+X−lv) → zTurn(u+X−lv)` is the remaining premise `hret`. The final vertex `V_end` is `slip_permit_Vend`. -/

namespace FLatticePaper.Sec3Permit

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet FLatticePaper.Sec3Shift

theorem slip_permit_freeV {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hW : StrongEstimates word)
    (hSE : StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    {w : Site} (hw : w ∈ (frameAt word).freeV) (hne : w ≠ (frameAt word).vLast)
    (hret : P.retained (zTurn (w + sec3X word - (frameAt word).sheetShift))
      (zTurn (w + (frameAt word).prescribedV 1 w + sec3X word - (frameAt word).sheetShift))) :
    (frameAt word).slip (standardField word) 1 (w + (frameAt word).prescribedV 1 w) ≤
      (frameAt word).slip (standardField word) 1 w := by
  by_cases he : EvenSite w
  · have hsw : w + sec3X word ∈ (frameAt word).closedPolygon :=
      SheetStars.even_shift_mem_of_freeV h hw he hne
    have hsu : w + (frameAt word).prescribedV 1 w + sec3X word ∈ (frameAt word).closedPolygon := by
      rw [SheetStars.prescribedV_even_one (frameAt word) he]
      exact SheetStars.u_even_shift_mem word h hw he hne
    exact Sec3Monotone.slip_le_of_retained h hW hSE P (FreeVH0.h0_eq_of_freeV h hW hSE hw)
      (SheetStars.h0_u_of_freeV h hW hSE hw hne) hsw hsu hret
  · have hsw : w + sec3X word ∈ (frameAt word).closedPolygon :=
      SheetStars.odd_shift_mem_of_freeV h hw he
    have hsu : w + (frameAt word).prescribedV 1 w + sec3X word ∈ (frameAt word).closedPolygon := by
      rw [SheetStars.prescribedV_odd_one (frameAt word) he]
      exact SheetStars.u_odd_shift_mem word h hw he
    exact Sec3Monotone.slip_le_of_retained h hW hSE P (FreeVH0.h0_eq_of_freeV h hW hSE hw)
      (SheetStars.h0_u_of_freeV h hW hSE hw hne) hsw hsu hret

end FLatticePaper.Sec3Permit
