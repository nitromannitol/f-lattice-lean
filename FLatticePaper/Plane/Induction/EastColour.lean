import FLatticePaper.Plane.Induction.HEasyP
import FLatticePaper.Plane.Induction.PolygonGeometry

/-! # The colour of the east neighbour of a short-`t` even H point

For an even `zf` with `2 ≤ t(zf) ≤ d − 1`, the east neighbour `q = zf + (1,0)` is odd, with inputs `q ± (0,1)`, and
`t(q) = t(zf) + n`, `t(incomingNeg q) = t(zf) + n + d`, `t(incomingPos q) = t(zf) + n − d`. All three lie in the zero band
`[1 − d, n + 2d − 1]` of `HasStrips`, so `q` is white by `HEasyP.lap_zero_of_band`. No deck translate is needed. -/

namespace FLatticePaper.EastColour

open FLatticePaper FLatticePaper.Induction

theorem lap_east_zero_of_small_t (frame : ChildFrame) {G : Field} (hS : frame.HasStrips G) {zf : Site}
    (hev : EvenSite zf) (ht1 : 2 ≤ frame.tGrade zf) (ht2 : frame.tGrade zf ≤ frame.child.den - 1) :
    laplacian G (zf + (1, 0)) = 0 := by
  obtain ⟨hn0, hnd, -, hd3, -⟩ := frame.child_facts
  have hodd : ¬ EvenSite (zf + (1, 0)) := by
    unfold EvenSite at hev ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hq : frame.tGrade (zf + (1, 0)) = frame.tGrade zf + frame.child.num := by
    unfold ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hN : frame.tGrade (incomingNeg (zf + (1, 0))) = frame.tGrade zf + frame.child.num + frame.child.den := by
    unfold incomingNeg
    rw [if_neg hodd]
    unfold ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hP : frame.tGrade (incomingPos (zf + (1, 0))) = frame.tGrade zf + frame.child.num - frame.child.den := by
    unfold incomingPos
    rw [if_neg hodd]
    unfold ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  apply HEasyP.lap_zero_of_band hS
  · rw [hq]
    constructor <;> linarith
  · rw [hN]
    constructor <;> linarith
  · rw [hP]
    constructor <;> linarith

end FLatticePaper.EastColour
