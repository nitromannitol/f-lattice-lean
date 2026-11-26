import FLatticePaper.Plane.Induction.M2White
import FLatticePaper.Plane.Induction.StripColours
import FLatticePaper.Plane.Induction.CanonForced

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

/-- **hderiv, west.** The west sign is `δ = -1`, `η = +1`, and `hfree_of_classes` gives `z ≠ vLast` for it, so the west case needs
the hypothesis `z ≠ vLast`; it is `M2White.hderiv_west_full` (the central reflection at `A - z`, with `lap_M2_zero`). -/
theorem hderiv_west_closed {G : Field} (frame : ChildFrame) (hP : frame.Packet G)
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
    (hzL : z ≠ frame.vLast) (hlapM1 : laplacian G (z.1 - 1, z.2) = 0) :
    FLatticePaper.SquareClauses.ForcedEdge G (fun _ _ => False) (z.1 - 1, z.2) (z.1 - 1, z.2 + 1) :=
  M2White.hderiv_west_full frame hP hprice hdrU hdrV hW1 hper hI hS hO hz hev hzF hzL hlapM1

/-- **`hcanon`, east sign (`δ = 1`).** The east `hderiv` holds for every even free root, so no sign hypothesis is needed. -/
theorem hcanon_east {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (C : CanonicalSignedPolicy frame G η) (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η)
    (hW : W.retained = C.policy) (hP : frame.Packet G)
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price G z ∧ frame.price G z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) = frame.price G z - 1)
    (hdrV : ∀ z, frame.price G (z + frame.child.modifiedDeck.transverse) = frame.price G z)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hper : ∀ z : Site, G (z + (frame.child.den, frame.child.num)) = G z)
    (hI : ∀ z, G (reflectionI - z) = G z)
    (hS : ∀ x : Site, 2 - 2 * frame.child.den ≤ frame.sGrade x →
      frame.sGrade x ≤ 2 * (frame.child.den + frame.child.num) - 2 → G x = harmonicGrid x)
    (hO : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x) :
    ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst → (η = -1 ∨ z ≠ frame.vLast) →
      laplacian G z = 0 → laplacian G (z.1 + 1, z.2) = 0 → laplacian G (z.1 + 1, z.2 - 1) = -1 →
      W.retained (z.1 + 1, z.2) (z.1 + 1, z.2 - 1) :=
  FLatticePaper.CanonForced.hcanon_of_deriv C W hW (δ := 1)
    (fun _ hz hev hF _ _ hlapM1 => hderiv_east_closed frame hP hprice hdrU hdrV hW1 hper hI hS hO hz hev hF hlapM1)

/-- **`hcanon`, west sign (`δ = -1`).** The sign `η = +1` excludes `z = vLast` in the disjunction of `hderiv`. -/
theorem hcanon_west {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} {η : ℤ}
    (C : CanonicalSignedPolicy frame G η) (W : FLatticePaper.W1Witness.OldPolicyWitness frame G seed η)
    (hW : W.retained = C.policy) (hη : η = 1) (hP : frame.Packet G)
    (hprice : ∀ z ∈ frame.closedPolygon, frame.cutPrice - 1 ≤ frame.price G z ∧ frame.price G z ≤ frame.cutPrice)
    (hdrU : ∀ z, frame.price G (z + frame.child.modifiedDeck.kernel) = frame.price G z - 1)
    (hdrV : ∀ z, frame.price G (z + frame.child.modifiedDeck.transverse) = frame.price G z)
    (hW1 : FLatticePaper.W1.W1Forced frame.child.num frame.child.den G)
    (hper : ∀ z : Site, G (z + (frame.child.den, frame.child.num)) = G z)
    (hI : ∀ z, G (reflectionI - z) = G z)
    (hS : ∀ x : Site, 2 - 2 * frame.child.den ≤ frame.sGrade x →
      frame.sGrade x ≤ 2 * (frame.child.den + frame.child.num) - 2 → G x = harmonicGrid x)
    (hO : ∀ x : Site, ¬ EvenSite x → 2 - 3 * frame.child.den + frame.child.num ≤ frame.sGrade x →
      frame.sGrade x ≤ 3 * frame.child.den + frame.child.num - 2 → G x = harmonicGrid x) :
    ∀ z ∈ frame.freeV, EvenSite z → z ≠ FLatticePaper.Induction.vFirst → (η = -1 ∨ z ≠ frame.vLast) →
      laplacian G z = 0 → laplacian G (z.1 + -1, z.2) = 0 → laplacian G (z.1 + -1, z.2 - -1) = -1 →
      W.retained (z.1 + -1, z.2) (z.1 + -1, z.2 - -1) :=
  FLatticePaper.CanonForced.hcanon_of_deriv C W hW (δ := -1)
    (fun _ hz hev hF hsc _ hlapM1 => hderiv_west_closed frame hP hprice hdrU hdrV hW1 hper hI hS hO hz hev hF
      (hsc.resolve_left (by omega)) hlapM1)

end FLatticePaper.HderivClosed
