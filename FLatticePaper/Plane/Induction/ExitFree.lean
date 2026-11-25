import FLatticePaper.Plane.Induction.ShapeOneGeom
import FLatticePaper.Plane.Induction.PriceDeck

/-! # The cone exit at height zero is a free H site (fan exit classification, step (A))

For a fan point `x` (odd, open) at height `1` above the base `z` (`x.2 = z.2 + 1`) with `x.1 ≥ z.1 + 1` (the odd cone condition) and
`n + 2 ≤ t(z)`, its south input `w = (x.1, z.2)` is an even site with `t(w) = t(z) + n(x.1 − z.1) ∈ [2, d + n − 2]`, lies in the closed polygon
(`s(w) = s(x) − (d − n)`), and its south neighbour `(x.1, z.2 − 1)` is outside the closed polygon (`t > d` there). So `w ∈ freeH`: the exit of the
cone at height zero is a free H site (Q23: "a strictly later H site"). The numerics (`scripts/w1_conj_fan_check.py`) show all 428 cone exits
are of this form. -/

namespace FLatticePaper.ExitFree

open FLatticePaper FLatticePaper.Induction

theorem freeH_of_height_zero_input (frame : ChildFrame) {z x : Site}
    (hz : frame.child.num + 2 ≤ frame.tGrade z) (hx : ¬ EvenSite x) (hxo : frame.openRect x)
    (hx2 : x.2 = z.2 + 1) (hl : z.1 + 1 ≤ x.1) :
    (x.1, x.2 - 1) ∈ frame.freeH := by
  obtain ⟨hn1, hnd, hdn, hd3, hP⟩ := frame.child_facts
  obtain ⟨a, c, ha, hc⟩ := FLatticePaper.PriceDeck.child_odd_witness frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hPpos : 0 ≤ frame.child.periodDenominator := by
    rw [hP]
    nlinarith
  have hxo' := hxo
  unfold ChildFrame.openRect at hxo'
  rw [if_neg hx] at hxo'
  obtain ⟨-, htxhi, hsxlo, hsxhi⟩ := hxo'
  have e : x.2 - 1 = z.2 := by omega
  have htw2 : frame.tGrade (x.1, x.2 - 1) = frame.tGrade z + frame.child.num * (x.1 - z.1) := by
    unfold ChildFrame.tGrade
    dsimp only
    rw [e]
    ring
  have htw1 : frame.tGrade (x.1, x.2 - 1) = frame.tGrade x + frame.child.den := by
    unfold ChildFrame.tGrade
    dsimp only
    ring
  have hsw : frame.sGrade (x.1, x.2 - 1) = frame.sGrade x - (frame.child.den - frame.child.num) := by
    unfold ChildFrame.sGrade
    dsimp only
    ring
  have hnl : frame.child.num ≤ frame.child.num * (x.1 - z.1) := by nlinarith
  have htlo : 2 ≤ frame.tGrade (x.1, x.2 - 1) := by linarith
  -- parity: `(x.1, x.2 − 1)` is even, so `t` is even (num and den are odd)
  have hpar : frame.tGrade (x.1, x.2 - 1) % 2 = 0 := by
    unfold ChildFrame.tGrade
    dsimp only
    rw [ha, hc]
    have hxe : (x.1 + x.2) % 2 = 1 := by
      unfold EvenSite at hx
      try simp only at hx
      omega
    have key : (2 * a + 1) * x.1 - (2 * c + 1) * (x.2 - 1)
        = 2 * (a * x.1 - c * (x.2 - 1)) + (x.1 - (x.2 - 1)) := by ring
    rw [key]
    generalize a * x.1 - c * (x.2 - 1) = K
    omega
  have hthi : frame.tGrade (x.1, x.2 - 1) ≤ frame.child.den + frame.child.num - 2 := by
    omega
  have hwe : EvenSite (x.1, x.2 - 1) := by
    unfold EvenSite at hx ⊢
    try simp only at hx ⊢
    omega
  -- the west closed-polygon point `w` (even): its inequalities
  have hclosed : (x.1, x.2 - 1) ∈ frame.closedPolygon := by
    unfold ChildFrame.closedPolygon
    simp only [Set.mem_setOf_eq]
    rw [if_pos hwe]
    have hs : frame.sGrade (x.1, x.2 - 1) = frame.sGrade x - (frame.child.den - frame.child.num) := hsw
    refine ⟨?_, ?_, ?_, ?_⟩
    · omega
    · exact hthi
    · omega
    · omega
  -- the south neighbour `(x.1, x.2 − 2)` is odd with `t > d`, so it is outside the closed polygon
  have hnot : ((x.1, x.2 - 1).1, (x.1, x.2 - 1).2 - 1) ∉ frame.closedPolygon := by
    intro hmem
    unfold ChildFrame.closedPolygon at hmem
    simp only [Set.mem_setOf_eq] at hmem
    have hodd : ¬ EvenSite ((x.1, x.2 - 1).1, (x.1, x.2 - 1).2 - 1) := by
      unfold EvenSite at hx ⊢
      try simp only at hx ⊢
      omega
    rw [if_neg hodd] at hmem
    have hts : frame.tGrade (x.1, x.2 - 1 - 1) = frame.tGrade (x.1, x.2 - 1) + frame.child.den := by
      unfold ChildFrame.tGrade
      dsimp only
      ring
    obtain ⟨hmt, hmt2, -⟩ := hmem
    have hmt2' : frame.tGrade (x.1, x.2 - 1 - 1) ≤ frame.child.den := hmt2
    omega
  have hspec : frame.hSpectrum (frame.tGrade (x.1, x.2 - 1)) := Or.inl ⟨hpar, htlo, hthi⟩
  unfold ChildFrame.freeH
  exact ⟨hclosed, hnot, hspec⟩

end FLatticePaper.ExitFree
