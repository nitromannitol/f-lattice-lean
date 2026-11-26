import FLatticePaper.Plane.Induction.RoutePresc
import FLatticePaper.Plane.Induction.C2Axial
import FLatticePaper.Plane.Induction.RouteRegion
import FLatticePaper.Plane.Induction.RouteSteps
import FLatticePaper.Plane.Induction.NonfreeBridge

/-! # The third arrow of the `h3` row: the north neighbour of an even free H root is strictly interior

For an even free H root `z` whose west neighbour `q = (z.1 - 1, z.2)` is a free H root, the point `p = (z.1, z.2 + 1)` is strictly
interior. With `t = t(z)`, `s = s(z)`: `t(p) = t - d`, `s(p) = s + (d - n)`. The even H spectrum gives `2 ≤ t ≤ d + n - 2`; the closed
odd `q` gives `s ≥ 2 + 2n` (from `s(q) = s - (d + n) ≥ 2 - d + n`) and `t ≤ d + n`; `RouteSteps.freeH_even_s_lt` gives
`s < T + 2 - 2d`; and `T > 2d - 2`. -/

namespace FLatticePaper.RouteH3

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1

theorem h3_source_strict (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z)
    (hq : (z.1 - 1, z.2) ∈ frame.freeH) :
    StrictInterior frame.child.num frame.child.den (z.1, z.2 + 1) := by
  obtain ⟨hn0, -, hd2, -, -⟩ := frame.child_facts
  have hTd : frame.child.periodDenominator
      = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
  have hs_lt : frame.sGrade z < frame.child.periodDenominator + 2 - 2 * frame.child.den :=
    FLatticePaper.Induction.RouteSteps.freeH_even_s_lt frame (x := z.1) (y := z.2) hz hev
  have hz' := hz
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz'
  obtain ⟨-, -, hzsp⟩ := hz'
  have hpar : frame.tGrade z % 2 = 0 := by
    rw [FLatticePaper.Induction.tGrade_parity frame z]
    exact hev
  have hzt : 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := by
    unfold ChildFrame.hSpectrum at hzsp
    omega
  have hqc := hq
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hqc
  obtain ⟨hqcl, -, -⟩ := hqc
  have hqcl' := (frame.mem_closedPolygon_iff (z.1 - 1, z.2)).mp hqcl
  have hqodd : ¬ EvenSite (z.1 - 1, z.2) := by
    intro h
    have h' : (z.1 - 1 + z.2) % 2 = 0 := h
    unfold EvenSite at hev
    omega
  have hqs : frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
    simp only [ChildFrame.sGrade]
    ring
  have hq3 : 2 - frame.child.den + frame.child.num ≤ frame.sGrade (z.1 - 1, z.2) := by
    rcases hqcl' with h | h
    · exact absurd h.1 hqodd
    · exact h.2.2.2.1
  have hq3' : 2 - frame.child.den + frame.child.num ≤ frame.sGrade z - (frame.child.den + frame.child.num) := by
    rw [← hqs]
    exact hq3
  have hpo : ¬ EvenSite (z.1, z.2 + 1) := by
    intro h
    have h' : (z.1 + (z.2 + 1)) % 2 = 0 := h
    unfold EvenSite at hev
    omega
  have hw1t : w1t frame.child.num frame.child.den (z.1, z.2 + 1) = frame.tGrade z - frame.child.den := by
    unfold w1t ChildFrame.tGrade
    ring
  have hw1s : w1s frame.child.num frame.child.den (z.1, z.2 + 1)
      = frame.sGrade z + (frame.child.den - frame.child.num) := by
    unfold w1s ChildFrame.sGrade
    ring
  have hTw : w1T frame.child.num frame.child.den = frame.child.periodDenominator := hTd.symm
  have hTbig : 2 * frame.child.den - 2 < frame.child.periodDenominator := by
    rw [hTd]
    nlinarith [mul_nonneg (show (0:ℤ) ≤ frame.child.den - frame.child.num - 2 by omega)
      (show (0:ℤ) ≤ frame.child.den + frame.child.num by omega),
      mul_pos hn0 (show (0:ℤ) < frame.child.den by omega)]
  unfold StrictInterior
  simp only [w1b, w1a, w1h, w1c, if_neg hpo]
  rw [hw1t, hw1s, hTw]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hzt.1, hzt.2, hq3', hs_lt, hTbig, hn0]

/-- **The third arrow of `h3`**: the north neighbour `p = (z.1, z.2 + 1)` of an even free H root keeps `z`, by the port argument with
zero shift (`h3_source_strict` and `not_strict_of_freeH`). -/
theorem h3_arrow_c {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0) {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z)
    (hq : (z.1 - 1, z.2) ∈ frame.freeH) :
    laplacian G (z.1, z.2 + 1) = -1 ∨ C.policy (z.1, z.2 + 1) z := by
  by_cases hb : laplacian G (z.1, z.2 + 1) = -1
  · exact Or.inl hb
  · right
    have hw : laplacian G (z.1, z.2 + 1) = 0 := (hbin _).resolve_left hb
    have hpo : ¬ EvenSite (z.1, z.2 + 1) := by
      intro h
      have h' : (z.1 + (z.2 + 1)) % 2 = 0 := h
      unfold EvenSite at hev
      omega
    have hs : EvenSite (0 : Site) := by
      unfold EvenSite
      norm_num
    have hT : ∀ x u, C.policy x u ↔ C.policy (x + 0) (u + 0) := fun x u => by simp
    have hqw : laplacian G ((z.1, z.2 + 1) + 0) = 0 := by simpa using hw
    have hqS : StrictInterior frame.child.num frame.child.den ((z.1, z.2 + 1) + 0) := by
      simpa using h3_source_strict frame hz hev hq
    have hin : z = incomingNeg (z.1, z.2 + 1) ∨ z = incomingPos (z.1, z.2 + 1) :=
      Or.inl (by unfold incomingNeg; rw [if_neg hpo]; ext <;> simp)
    have hport : ¬ StrictInterior frame.child.num frame.child.den (z + 0) := by
      simpa using FLatticePaper.C2Axial.not_strict_of_freeH (frame := frame) hz
    exact FLatticePaper.RouteRegion.route_port_arrow C hW1 hs hT hqw hqS hin hport

end FLatticePaper.RouteH3
