import FLatticePaper.Plane.Induction.CapRecursion
import FLatticePaper.Plane.Induction.PolygonGeometry

/-! # Whiteness of the V route sites from the harmonic stencil (the M2 pattern)

A site is white when its value and both inputs equal the harmonic grid (the Laplacian of the harmonic grid vanishes, and the
Laplacian is `g(neg) − g(c) + g(pos) − g(c)`). The even strip `2 − 2d ≤ s ≤ 2L − 2` gives the harmonic value at even sites, and the
odd extension `2 − 3d + n ≤ s ≤ 3d + n − 2` at odd sites. An even centre has odd inputs and an odd centre has even inputs. -/

namespace FLatticePaper.WhiteRoute

open Farey FLatticePaper FLatticePaper.Induction

/-- A site whose value and both inputs are harmonic is white. -/
theorem lap_zero_of_harm {G : Field} {c : Site} (h0 : G c = harmonicGrid c)
    (h1 : G (incomingNeg c) = harmonicGrid (incomingNeg c)) (h2 : G (incomingPos c) = harmonicGrid (incomingPos c)) :
    laplacian G c = 0 := by
  have hlap := harmonicGrid_harmonic c
  unfold laplacian at hlap ⊢
  rw [h0, h1, h2]
  linarith

/-- **An even centre is white** when it is in the even strip and its (odd) inputs are in the odd extension. -/
theorem lap_zero_even_centre (frame : ChildFrame) {G : Field}
    (hS : ∀ x : Site, 2 - 2 * frame.child.den ≤ frame.sGrade x → frame.sGrade x ≤ 2 * (frame.child.den + frame.child.num) - 2 →
      G x = harmonicGrid x)
    (hO : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x)
    {c : Site} (hev : EvenSite c)
    (hc1 : 2 - 2 * frame.child.den ≤ frame.sGrade c) (hc2 : frame.sGrade c ≤ 2 * (frame.child.den + frame.child.num) - 2)
    (hi1 : 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade (incomingNeg c))
    (hi2 : frame.sGrade (incomingNeg c) ≤ 3 * frame.child.den + frame.child.num - 2)
    (hi3 : 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade (incomingPos c))
    (hi4 : frame.sGrade (incomingPos c) ≤ 3 * frame.child.den + frame.child.num - 2) :
    laplacian G c = 0 := by
  have hn : ¬ EvenSite (incomingNeg c) := by
    rw [FLatticePaper.CapRecursion.incomingNeg_of_even' c hev]
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have hp : ¬ EvenSite (incomingPos c) := by
    rw [FLatticePaper.CapRecursion.incomingPos_of_even' c hev]
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  exact lap_zero_of_harm (hS c hc1 hc2) (hO _ hn hi1 hi2) (hO _ hp hi3 hi4)

/-- **An odd centre is white** when it is in the odd extension and its (even) inputs are in the even strip. -/
theorem lap_zero_odd_centre (frame : ChildFrame) {G : Field}
    (hS : ∀ x : Site, 2 - 2 * frame.child.den ≤ frame.sGrade x → frame.sGrade x ≤ 2 * (frame.child.den + frame.child.num) - 2 →
      G x = harmonicGrid x)
    (hO : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x)
    {c : Site} (hodd : ¬ EvenSite c)
    (hc1 : 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade c) (hc2 : frame.sGrade c ≤ 3 * frame.child.den + frame.child.num - 2)
    (hi1 : 2 - 2 * frame.child.den ≤ frame.sGrade (incomingNeg c))
    (hi2 : frame.sGrade (incomingNeg c) ≤ 2 * (frame.child.den + frame.child.num) - 2)
    (hi3 : 2 - 2 * frame.child.den ≤ frame.sGrade (incomingPos c))
    (hi4 : frame.sGrade (incomingPos c) ≤ 2 * (frame.child.den + frame.child.num) - 2) :
    laplacian G c = 0 := by
  have hn : EvenSite (incomingNeg c) := by
    rw [FLatticePaper.CapRecursion.incomingNeg_of_odd' c hodd]
    unfold EvenSite at hodd ⊢
    simp only at hodd ⊢
    omega
  have hp : EvenSite (incomingPos c) := by
    rw [FLatticePaper.CapRecursion.incomingPos_of_odd' c hodd]
    unfold EvenSite at hodd ⊢
    simp only at hodd ⊢
    omega
  exact lap_zero_of_harm (hO c hodd hc1 hc2) (hS _ hi1 hi2) (hS _ hi3 hi4)

end FLatticePaper.WhiteRoute
