import FLatticePaper.Plane.Induction.HEasyP
import FLatticePaper.Plane.Induction.RouteRegional
import FLatticePaper.Plane.Induction.C2Axial

/-! # The second arrow of the `h3` row in the easy regime (`d < 3n − 2`)

For an even free H root `z` with the free west neighbour `b = z − (1, 0)`, the middle source `m = (z.1 − 1, z.2 + 1)` and the middle
target `p = (z.1, z.2 + 1) = incomingPos m`. If `m` is strictly interior and the target `p` is white, `white_route_policy` keeps
`p` at `m` (the input `z` of `p` is not strictly interior, `z ≠ m`). The whiteness of `p` is an explicit hypothesis here: it is
`HEasyP.lap_p_zero_of_free` when `d + 1 ≤ t(z)`, and the open claim (Q37) when `t(z) ≤ d`. -/

namespace FLatticePaper.RouteH3Easy

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1

/-- **The second arrow of `h3`, with the target white.** -/
theorem h3_arrow_easy {frame : ChildFrame} {G : Field} {η : ℤ} (C : CanonicalSignedPolicy frame G η)
    (hW1 : W1Forced frame.child.num frame.child.den G)
    (hbin : ∀ c, laplacian G c = -1 ∨ laplacian G c = 0)
    {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z)
    (hm : StrictInterior frame.child.num frame.child.den (z.1 - 1, z.2 + 1))
    (hpw : laplacian G (z.1, z.2 + 1) = 0) :
    laplacian G (z.1 - 1, z.2 + 1) = -1 ∨ C.policy (z.1 - 1, z.2 + 1) (z.1, z.2 + 1) := by
  by_cases hb : laplacian G (z.1 - 1, z.2 + 1) = -1
  · exact Or.inl hb
  · right
    have hmw : laplacian G (z.1 - 1, z.2 + 1) = 0 := (hbin _).resolve_left hb
    have hmev : EvenSite (z.1 - 1, z.2 + 1) := by
      unfold EvenSite at hev ⊢
      simp only at hev ⊢
      omega
    have hpodd : ¬ EvenSite (z.1, z.2 + 1) := by
      unfold EvenSite at hev ⊢
      simp only at hev ⊢
      omega
    have hin : (z.1, z.2 + 1) = incomingNeg (z.1 - 1, z.2 + 1) ∨
        (z.1, z.2 + 1) = incomingPos (z.1 - 1, z.2 + 1) := by
      refine Or.inr ?_
      unfold incomingPos
      rw [if_pos hmev]
      refine Prod.ext ?_ ?_
      · simp
      · simp
    have hzin : z = incomingNeg (z.1, z.2 + 1) ∨ z = incomingPos (z.1, z.2 + 1) := by
      refine Or.inl ?_
      unfold incomingNeg
      rw [if_neg hpodd]
      refine Prod.ext ?_ ?_
      · simp
      · simp
    have hzR := FLatticePaper.C2Axial.not_strict_of_freeH hz
    have hzm : z ≠ (z.1 - 1, z.2 + 1) := by
      intro h
      have h1 : z.1 = z.1 - 1 := congrArg Prod.fst h
      omega
    exact FLatticePaper.RouteRegional.white_route_policy C hW1 hm hmw hin hpw hzin hzR hzm

end FLatticePaper.RouteH3Easy
