import FLatticePaper.Plane.Induction.M2White
import FLatticePaper.Plane.Induction.StripColours

/-! # hderiv east, with the `vLast` case closed by the strip colours

`M2White.hderiv_east_full` carried the hypothesis `z ≠ vLast ∨ 2n ≤ d`. Here the case `z = vLast` is closed: the east middle
`vLast + (1,0)` has Laplacian `-1` (`StripColours.lap_vLast_east`), so the hypothesis `laplacian G (z.1+1, z.2) = 0` fails and
the statement is vacuous there. Every other root goes through the regime split as before. -/

namespace FLatticePaper.HderivClosed

open FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.W1 FLatticePaper.W1NonfreeOut

/-- **hderiv, east, all even free V roots.** -/
theorem hderiv_east_closed {G : Field} (frame : ChildFrame) (hP : frame.Packet G)
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price G z ∧ frame.price G z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) = frame.price G z - 1)
    (hdrV : ∀ z, frame.price G (z + frame.child.modifiedDeck.transverse) = frame.price G z)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hper : ∀ z : Site, G (z + (frame.child.den, frame.child.num)) = G z)
    (hI : ∀ z, G (reflectionI - z) = G z)
    (hS : ∀ x : Site, 2 - 2 * frame.child.den ≤ frame.sGrade x →
      frame.sGrade x ≤ 2 * (frame.child.den + frame.child.num) - 2 → G x = harmonicGrid x)
    (hO : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x)
    {z : Site} (hz : z ∈ frame.freeV) (hev : EvenSite z) (hzF : z ≠ FLatticePaper.Induction.vFirst)
    (hlapM1 : laplacian G (z.1 + 1, z.2) = 0) :
    FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (z.1 + 1, z.2) (z.1 + 1, z.2 - 1) := by
  by_cases hv : z = frame.vLast
  · exfalso
    subst hv
    rw [StripColours.lap_vLast_east frame hP.strips hP.periods] at hlapM1
    norm_num at hlapM1
  · by_cases h : frame.child.den < 2 * frame.child.num
    · exact FLatticePaper.HardEast.hderiv_regime frame hP hprice hdrU hdrV hW1 hper h hI hz hev hzF hv
    · exact hderiv_easy frame hW1 hz hev hzF hlapM1 (M2White.lap_M2_zero frame hS hO hz hev (by omega))

end FLatticePaper.HderivClosed
