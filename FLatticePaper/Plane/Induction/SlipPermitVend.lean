import FLatticePaper.Plane.Induction.FinalRootSlip
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.RankFromForts

/-! The permit at the final V vertex `vLast = I + V` (the exempt root of the note's §1). Its prescribed sign `+1` input is `vLast + (1,0)`,
which lies in the closed polygon, so its slip is at most `2` (`slipRange`), while the slip at `vLast` is `2` (`slip_vLast`). -/

namespace FLatticePaper.SlipPermitVend

open Farey FLatticePaper FLatticePaper.Induction

theorem vLast_add_mem_closedPolygon (frame : ChildFrame) :
    frame.vLast + (1, 0) ∈ frame.closedPolygon := by
  obtain ⟨h1, h2, h3, h4, hT⟩ := frame.child_facts
  have hodd : ¬ EvenSite (frame.vLast + (1, 0)) := by
    unfold EvenSite ChildFrame.vLast
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have ht : frame.tGrade (frame.vLast + (1, 0)) =
      frame.child.den + 2 * frame.child.num - frame.child.periodDenominator := by
    rw [hT]
    unfold ChildFrame.tGrade ChildFrame.vLast
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hs : frame.sGrade (frame.vLast + (1, 0)) = frame.child.den + 3 * frame.child.num := by
    unfold ChildFrame.sGrade ChildFrame.vLast
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  rw [ChildFrame.mem_closedPolygon_iff, ht, hs, hT]
  right
  refine ⟨hodd, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem slip_permit_Vend {word : Word} (hW : StrongEstimates word) :
    slipPermits (standardField word) (fun z => standardField word (z + (frameAt word).shortShift))
      (frameAt word).vLast ((frameAt word).vLast + (1, 0)) := by
  have hc := FinalRootSlip.slip_vLast (frameAt word) hW.packet (η := 1) (Or.inl rfl)
  have hr := hW.slipRange _ (vLast_add_mem_closedPolygon (frameAt word))
  unfold ChildFrame.slip at hc hr
  unfold slipPermits slipIncrement
  dsimp only
  simp only [one_smul] at hc hr
  linarith [hc, hr.2]

end FLatticePaper.SlipPermitVend
