import FLatticePaper.Plane.Induction.PhaseOneWindow
import FLatticePaper.Plane.Induction.PsiCalibration
import FLatticePaper.Plane.Induction.ArcPsi

/-! `A(reflH i) = 0` in phase one, for the prescribed neighbour `i` of a non-`H_0` free H root.

In phase one `sheetShift = 0`, so `A = FqW`, and `FqW w = G(Z w) + harmonicGrid w`. The conjugate's s-grade at `Z w` is `2(T_p(w) − N)`.
For `w = reflH i`, `T_p(w) = 1 + N + D − T_p(i)`, which lies in `[1−D, 2D+N−1]` by the neighbour window. The harmonic strip of the conjugate
then gives `G(Z w) = harmonicGrid (Z w) = −harmonicGrid w` (`harmonicGrid_Z`), so `FqW w = 0`. -/

namespace FLatticePaper.PhaseOneA

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.PsiCalibration

theorem A_refl_zero {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) (hSE : StrongEstimates (conjWord word))
    (hW1 : (frameAt word).eps = 1) {r : Site} (hr : r ∈ (frameAt word).freeH) (hr1 : r ≠ hFirst) (η : ℤ) :
    (frameAt word).sheetA (FqW word) (FLatticePaper.ArcPsi.reflH word (r + (frameAt word).prescribedH η r)) = 0 := by
  obtain ⟨hN1, hND, hD2, hnq, hdq, hn_eq, hd_eq, heps, -⟩ := FLatticePaper.PriceInputs.pdata h
  have hrel : (frameAt word).parents.odd.num * (frameAt word).child.den -
      (frameAt word).child.num * (frameAt word).parents.odd.den = 1 := by
    rw [hd_eq, hn_eq]
    linear_combination hW1 - heps
  have hwin := FLatticePaper.PhaseOneWindow.tp_neighbour_window (frameAt word) hN1 hND hrel hr hr1 η
  obtain ⟨hcn, hcd⟩ := frameAt_conj_num_den h
  have hS := hSE.packet.strips
  have hTw : (frameAt word).parents.odd.num * (FLatticePaper.ArcPsi.reflH word (r + (frameAt word).prescribedH η r)).1 -
      (frameAt word).parents.odd.den * (FLatticePaper.ArcPsi.reflH word (r + (frameAt word).prescribedH η r)).2 =
      1 + (frameAt word).parents.odd.num + (frameAt word).parents.odd.den -
        ((frameAt word).parents.odd.num * (r + (frameAt word).prescribedH η r).1 -
          (frameAt word).parents.odd.den * (r + (frameAt word).prescribedH η r).2) := by
    unfold FLatticePaper.ArcPsi.reflH
    linear_combination hrel
  have hsG : standardField (conjWord word)
      (i3Z (FLatticePaper.ArcPsi.reflH word (r + (frameAt word).prescribedH η r))) =
      harmonicGrid (i3Z (FLatticePaper.ArcPsi.reflH word (r + (frameAt word).prescribedH η r))) := by
    apply hS.2
    · rw [sGrade_conj word h, hcd]
      unfold i3Z
      simp only
      linarith [hwin.1, hwin.2, hTw]
    · rw [sGrade_conj word h, hcd, hcn]
      unfold i3Z
      simp only
      linarith [hwin.1, hwin.2, hTw]
  unfold ChildFrame.sheetA
  rw [sheetShift_W1 word hW1, sub_zero]
  unfold FqW
  rw [quarterTurnField_apply, hsG, harmonicGrid_Z]
  ring

end FLatticePaper.PhaseOneA
