import FLatticePaper.Plane.Induction.RouteH3

/-! # The middle target of the `h3` second arrow is white when its `q` lies in the zero band (`1 − d ≤ t(q)`)

For an even site `z`, the odd site `p = z + (0,1)` has incoming sites `incomingNeg p = z` and `incomingPos p = q = z + (0,2)`.
Its Laplacian is `G z + G q − 2 G p`. With the grades `t(p) = t(z) − d`, `t(q) = t(z) − 2d`, the three sites lie in the zero band
`1 − d ≤ t ≤ n + 2d − 1` of the strips whenever `1 − d ≤ t(q)` and `t(z) ≤ n + 2d − 1`; there `G` vanishes, so `lap p = 0`. -/

namespace FLatticePaper.HEasyP

open FLatticePaper FLatticePaper.Induction

/-- The zero band of the strips: a site whose `t` lies in `[1 − d, n + 2d − 1]` has `G = 0`. -/
theorem lap_zero_of_band {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) {x : Site}
    (hx : 1 - frame.child.den ≤ frame.tGrade x ∧ frame.tGrade x ≤ frame.child.num + 2 * frame.child.den - 1)
    (hn : 1 - frame.child.den ≤ frame.tGrade (incomingNeg x) ∧
      frame.tGrade (incomingNeg x) ≤ frame.child.num + 2 * frame.child.den - 1)
    (hp : 1 - frame.child.den ≤ frame.tGrade (incomingPos x) ∧
      frame.tGrade (incomingPos x) ≤ frame.child.num + 2 * frame.child.den - 1) :
    laplacian G x = 0 := by
  unfold laplacian
  rw [hS.1 _ hn.1 hn.2, hS.1 _ hp.1 hp.2, hS.1 _ hx.1 hx.2]
  ring

/-- **The middle target `p = z + (0,1)` of an even site `z` is white** when its far input `q = z + (0,2)` lies in the zero band
(`1 − d ≤ t(q)`) and `t(z)` is below the top of the band. -/
theorem lap_p_zero_of_t {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) {z : Site} (hev : EvenSite z)
    (hq : 1 - frame.child.den ≤ frame.tGrade (z.1, z.2 + 2))
    (hz : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1) :
    laplacian G (z.1, z.2 + 1) = 0 := by
  have hodd : ¬ EvenSite (z.1, z.2 + 1) := by
    unfold EvenSite at hev ⊢
    simp only
    omega
  have eN : incomingNeg (z.1, z.2 + 1) = z := by
    unfold incomingNeg
    rw [if_neg hodd]
    refine Prod.ext ?_ ?_ <;> simp
  have eP : incomingPos (z.1, z.2 + 1) = (z.1, z.2 + 2) := by
    unfold incomingPos
    rw [if_neg hodd]
    refine Prod.ext ?_ ?_
    · simp
    · simp; ring
  have tp : frame.tGrade (z.1, z.2 + 1) = frame.tGrade z - frame.child.den := by
    unfold ChildFrame.tGrade
    ring
  have tq : frame.tGrade (z.1, z.2 + 2) = frame.tGrade z - 2 * frame.child.den := by
    unfold ChildFrame.tGrade
    ring
  have hd : 1 ≤ frame.child.den := by
    obtain ⟨-, -, -, hd3, -⟩ := frame.child_facts
    omega
  apply lap_zero_of_band hS
  · rw [tp]
    constructor <;> omega
  · rw [eN]
    constructor <;> omega
  · rw [eP, tq]
    constructor <;> omega

/-- **The `h3` middle target of an even free H root `z` with `d + 1 ≤ t(z)`** (the case `1 − d ≤ t(q)`): the Laplacian at
`p = z + (0,1)` vanishes. -/
theorem lap_p_zero_of_free {frame : ChildFrame} {G : Field} (hS : frame.HasStrips G) {z : Site}
    (hz : z ∈ frame.freeH) (hev : EvenSite z) (ht : frame.child.den + 1 ≤ frame.tGrade z) :
    laplacian G (z.1, z.2 + 1) = 0 := by
  have hz' := hz
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz'
  obtain ⟨-, -, hsp⟩ := hz'
  have hup : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1 := by
    obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
    unfold ChildFrame.hSpectrum at hsp
    rcases hsp with h | h <;> omega
  apply lap_p_zero_of_t hS hev
  · have e : frame.tGrade (z.1, z.2 + 2) = frame.tGrade z - 2 * frame.child.den := by
      unfold ChildFrame.tGrade
      ring
    rw [e]
    omega
  · exact hup

end FLatticePaper.HEasyP
