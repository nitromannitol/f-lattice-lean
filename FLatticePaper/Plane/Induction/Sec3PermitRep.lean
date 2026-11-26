import FLatticePaper.Plane.Induction.PsiRep
import FLatticePaper.Plane.Induction.SheetStars
import FLatticePaper.Plane.Induction.FreeVH0
import FLatticePaper.Plane.Induction.Sec3Monotone
import FLatticePaper.Plane.Induction.StrongCoreDef

/-! The §3 permit for free V whites `w ≠ V_end` with the native-edge retention replaced: the premise is the prescription of the
canonical policy at the free points (`PrescribedAt`), and the Ψ inequality comes from `PsiRep.psi_le_of_rep`.

`D₊(u) ≤ D₊(w)` for `u = w + prescribedV 1 w`. The final vertex `V_end` is `SlipPermitVend.slip_permit_Vend`. -/

namespace FLatticePaper.Sec3PermitRep

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.Sec3Shift FLatticePaper.W1MSheet FLatticePaper.W1Step

theorem slip_permit_freeV_psi {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hW : StrongCore word)
    (hSE : StrongEstimates (conjWord word)) {seed : Site → Site → Prop}
    (P : OldPolicyData (frameAt (conjWord word)) (standardField (conjWord word)) seed (frameAt word).eps)
    (hPres : PrescribedAt (frameAt (conjWord word)) (standardField (conjWord word)) (frameAt word).eps P.retained)
    {w : Site} (hw : w ∈ (frameAt word).freeV) (hne : w ≠ (frameAt word).vLast) :
    (frameAt word).slip (standardField word) 1 (w + (frameAt word).prescribedV 1 w) ≤
      (frameAt word).slip (standardField word) 1 w := by
  have hpsi := PsiRep.psi_le_of_rep h hSE P hPres hw hne
  have hwF := FreeVH0.h0_eq_of_freeV h hW hSE hw
  have huF := SheetStars.h0_u_of_freeV h hW hSE hw hne
  by_cases he : EvenSite w
  · have hsw : w + sec3X word ∈ (frameAt word).closedPolygon :=
      SheetStars.even_shift_mem_of_freeV h hw he hne
    have hsu : w + (frameAt word).prescribedV 1 w + sec3X word ∈ (frameAt word).closedPolygon := by
      rw [SheetStars.prescribedV_even_one (frameAt word) he]
      exact SheetStars.u_even_shift_mem word h hw he hne
    rw [Sec3Monotone.slip_eq_neg_min_sheetPsi h hW hSE huF hsu,
      Sec3Monotone.slip_eq_neg_min_sheetPsi h hW hSE hwF hsw]
    have hmin : min 0 (sheetPsi word (w + sec3X word)) ≤ min 0 (sheetPsi word (w + (frameAt word).prescribedV 1 w + sec3X word)) :=
      min_le_min le_rfl hpsi
    linarith
  · have hsw : w + sec3X word ∈ (frameAt word).closedPolygon :=
      SheetStars.odd_shift_mem_of_freeV h hw he
    have hsu : w + (frameAt word).prescribedV 1 w + sec3X word ∈ (frameAt word).closedPolygon := by
      rw [SheetStars.prescribedV_odd_one (frameAt word) he]
      exact SheetStars.u_odd_shift_mem word h hw he
    rw [Sec3Monotone.slip_eq_neg_min_sheetPsi h hW hSE huF hsu,
      Sec3Monotone.slip_eq_neg_min_sheetPsi h hW hSE hwF hsw]
    have hmin : min 0 (sheetPsi word (w + sec3X word)) ≤ min 0 (sheetPsi word (w + (frameAt word).prescribedV 1 w + sec3X word)) :=
      min_le_min le_rfl hpsi
    linarith

end FLatticePaper.Sec3PermitRep
