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

/-- **The east neighbour of a late even H point is white (Q38).** For an even `zf` with `d ≤ t(zf) ≤ d + n − 2`, the east neighbour
`q = zf + (1,0)` has `G q = 0` by the ordinary zero band (`t q ∈ [d + n, d + 2n − 2]`), its positive input `zf + (1,1)` by the band too
(`t ∈ [n, 2n − 2]`), and its negative input `zf + (1,−1)` in the child's upper extended even zero interval `[n + 2d − 1, 2L − 2]`,
where the input `hZ` gives zero (for the standard field, `W1Strips.even_zero_full`). -/
theorem lap_east_zero_of_late_t (frame : ChildFrame) {G : Field} (hS : frame.HasStrips G)
    (hZ : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → G w = 0)
    {zf : Site} (hev : EvenSite zf) (ht1 : frame.child.den ≤ frame.tGrade zf)
    (ht2 : frame.tGrade zf ≤ frame.child.den + frame.child.num - 2) :
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
  have hevN : EvenSite (incomingNeg (zf + (1, 0))) := by
    unfold incomingNeg
    rw [if_neg hodd]
    unfold EvenSite at hev ⊢
    simp only [Prod.fst_add, Prod.snd_add]
    omega
  have hGq : G (zf + (1, 0)) = 0 := hS.1 _ (by rw [hq]; linarith) (by rw [hq]; linarith)
  have hGp : G (incomingPos (zf + (1, 0))) = 0 :=
    hS.1 _ (by rw [hP]; linarith) (by rw [hP]; linarith)
  have hGn : G (incomingNeg (zf + (1, 0))) = 0 :=
    hZ _ hevN (by rw [hN]; linarith) (by rw [hN]; linarith)
  unfold laplacian
  rw [hGn, hGp, hGq]
  ring

/-- **The east neighbour of every even H point of the H spectrum is white.** For an even `zf` with `2 ≤ t(zf) ≤ d + n − 2`, the
east neighbour `zf + (1,0)` is white: the short half `t(zf) ≤ d − 1` by `lap_east_zero_of_small_t` (no input), the late half
`t(zf) ≥ d` by `lap_east_zero_of_late_t` (with the extended even zero input `hZ`). -/
theorem lap_east_zero_of_even_H (frame : ChildFrame) {G : Field} (hS : frame.HasStrips G)
    (hZ : ∀ w : Site, EvenSite w → frame.child.num + 2 * frame.child.den - 1 ≤ frame.tGrade w →
      frame.tGrade w ≤ 2 * (frame.child.den + frame.child.num) - 2 → G w = 0)
    {zf : Site} (hev : EvenSite zf) (ht1 : 2 ≤ frame.tGrade zf)
    (ht2 : frame.tGrade zf ≤ frame.child.den + frame.child.num - 2) :
    laplacian G (zf + (1, 0)) = 0 := by
  by_cases h : frame.tGrade zf ≤ frame.child.den - 1
  · exact lap_east_zero_of_small_t frame hS hev ht1 h
  · exact lap_east_zero_of_late_t frame hS hZ hev (by omega) ht2

end FLatticePaper.EastColour
