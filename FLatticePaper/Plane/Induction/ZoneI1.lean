import FLatticePaper.Plane.Induction.ZoneCase
import FLatticePaper.Plane.Induction.StrongEstimates
import FLatticePaper.Plane.Induction.PolygonGeometry
import FLatticePaper.Plane.Induction.Packet

/-! # The frame-level facts of the zone of I1 (task 49, the wrapper of step (d))

For the earlier word `u` with child `(D − N, D + N)` (so `N = parentN u`, `D = parentD u`), the packet periods of the standard
field give the kernel and transverse relations used by `ZoneHyp`, with the coherent constants `0` and `−(B + D)`.
-/

namespace FLatticePaper.Induction
open Farey FLatticePaper

namespace ZoneI1

/-- The value of the harmonic grid from its numerator. -/
theorem harmonicGrid_of_numerator (x : Site) (k : ℤ)
    (h : x.1 ^ 2 + 2 * x.1 * x.2 - x.2 ^ 2 - 2 * x.2 - (x.1 + x.2) % 2 = 4 * k) : harmonicGrid x = k := by
  unfold harmonicGrid
  rw [h]
  exact Int.mul_ediv_cancel_left k (by norm_num)

/-- The kernel of the child `(D − N, D + N)` (even) is `(D + N, D − N)`. -/
theorem kernel_of_even (U : ChildFrame) : U.child.modifiedDeck.kernel = (U.child.den, U.child.num) := by
  have he : (U.child.num + U.child.den) % 2 = 0 := U.child_even
  unfold Fraction.modifiedDeck Fraction.periodMultiplicity
  rw [if_pos he]
  simp

/-- The transverse vector of the child is `(num − den, num + den)`. -/
theorem transverse_of_child (U : ChildFrame) :
    U.child.modifiedDeck.transverse = (U.child.num - U.child.den, U.child.num + U.child.den) := by
  unfold Fraction.modifiedDeck Fraction.unmodifiedDeck
  rfl

/-- The coherent constant of the kernel is zero (integer form, child `(b, r) = (D − N, D + N)`). -/
theorem cU_value (D N b r : ℤ) (hb : b = D - N) (hr : r = D + N) :
    harmonicGrid (b - r + 1, b + r - 1) - (b * (b - r + 1) - r * (b + r - 1))
      + ((r + b) - (r ^ 2 + 2 * r * b - b ^ 2)) / 2 = 0 := by
  subst hb hr
  have hh : harmonicGrid ((D - N) - (D + N) + 1, (D - N) + (D + N) - 1) = D + N ^ 2 - 2 * D * N - D ^ 2 := by
    apply harmonicGrid_of_numerator
    have hp : ((D - N) - (D + N) + 1 + ((D - N) + (D + N) - 1)) % 2 = 0 := by omega
    rw [hp]
    ring
  rw [hh]
  have hd : ((D + N) + (D - N) - ((D + N) ^ 2 + 2 * (D + N) * (D - N) - (D - N) ^ 2)) / 2
      = D + N ^ 2 - 2 * D * N - D ^ 2 := by
    rw [show (D + N) + (D - N) - ((D + N) ^ 2 + 2 * (D + N) * (D - N) - (D - N) ^ 2)
        = 2 * (D + N ^ 2 - 2 * D * N - D ^ 2) by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [hd]
  ring

/-- The coherent constant of the transverse is `−(B + D)` (integer form). -/
theorem cV_value (D N b r : ℤ) (hb : b = D - N) (hr : r = D + N) :
    ((r + b) - (r ^ 2 + 2 * r * b - b ^ 2)) / 2 - (b * (b + 1) - r * (2 * b + r - 1))
      + (b * (b - r) - r * (b + r)) = -(D ^ 2 + 2 * D * N - N ^ 2 + D) := by
  subst hb hr
  have hd : ((D + N) + (D - N) - ((D + N) ^ 2 + 2 * (D + N) * (D - N) - (D - N) ^ 2)) / 2
      = D - (D ^ 2 + 2 * D * N - N ^ 2) := by
    rw [show (D + N) + (D - N) - ((D + N) ^ 2 + 2 * (D + N) * (D - N) - (D - N) ^ 2)
        = 2 * (D - (D ^ 2 + 2 * D * N - N ^ 2)) by ring]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [hd]
  ring

/-- The packet periods of the earlier standard field, in the form of `ZoneHyp`: the kernel `(D + N, D − N)` is a zero period
and the transverse `(−2N, 2D)` shifts by `t(y) − (B + D)`. -/
theorem periods_of_packet (U : ChildFrame) (F : Field) (hP : U.Packet F) (N D : ℤ)
    (hb : U.child.num = D - N) (hr : U.child.den = D + N) :
    (∀ y : Site, F (y + (D + N, D - N)) = F y) ∧
    (∀ y : Site, F (y + (-2 * N, 2 * D)) = F y + ((D - N) * y.1 - (D + N) * y.2)
      - (D ^ 2 + 2 * D * N - N ^ 2 + D)) := by
  obtain ⟨p1, p2⟩ := hP.periods
  have hU : U.coherentConstantU = 0 := by
    have e : U.child.modifiedDeck.transverse + (1, -1)
        = (U.child.num - U.child.den + 1, U.child.num + U.child.den - 1) := by
      rw [transverse_of_child U]
      ext
      · simp
      · simp; ring
    unfold ChildFrame.coherentConstantU ChildFrame.symmetryConstant ChildFrame.tGrade
    rw [e]
    unfold Fraction.periodDenominator
    have := cU_value D N U.child.num U.child.den hb hr
    linear_combination this
  have hV : U.coherentConstantV = -(D ^ 2 + 2 * D * N - N ^ 2 + D) := by
    have e2 : U.child.modifiedDeck.kernel + U.child.modifiedDeck.transverse + (1, -1)
        = (U.child.num + 1, 2 * U.child.num + U.child.den - 1) := by
      rw [kernel_of_even U, transverse_of_child U]
      ext
      · simp
      · simp; ring
    unfold ChildFrame.coherentConstantV ChildFrame.symmetryConstant ChildFrame.centre ChildFrame.tGrade
    rw [e2, transverse_of_child U]
    unfold Fraction.periodDenominator
    have := cV_value D N U.child.num U.child.den hb hr
    linear_combination this
  constructor
  · intro y
    have h := p1 y
    rw [kernel_of_even U, hU, hr, hb] at h
    simpa using h
  · intro y
    have h := p2 y
    rw [transverse_of_child U, hV, hb, hr] at h
    unfold Fraction.transverseGrade at h
    rw [hb, hr] at h
    have e : ((D - N) - (D + N), (D - N) + (D + N)) = (-2 * N, 2 * D) := by
      ext
      · first | (simp; done) | (simp; ring)
      · first | (simp; done) | (simp; ring)
    rw [e] at h
    linear_combination h

/-- The polygon of the zone is inside the closed polygon of the earlier child. -/
theorem polyU_closed (U : ChildFrame) (N D : ℤ) (hb : U.child.num = D - N) (hr : U.child.den = D + N) (y : Site)
    (hP : ZoneSlip.PolyU N D y) : y ∈ U.closedPolygon := by
  have hT : U.child.periodDenominator = 2 * (D ^ 2 + 2 * D * N - N ^ 2) := by
    unfold Fraction.periodDenominator
    rw [hb, hr]
    ring
  have hs : U.sGrade y = 2 * D * y.1 + 2 * N * y.2 := by
    unfold ChildFrame.sGrade
    rw [hb, hr]
    ring
  have ht : U.tGrade y = (D - N) * y.1 - (D + N) * y.2 := by
    unfold ChildFrame.tGrade
    rw [hb, hr]
  simp only [ChildFrame.closedPolygon, Set.mem_setOf_eq]
  rcases hP with ⟨he, h1, h2, h3, h4⟩ | ⟨hne, h1, h2, h3, h4⟩
  · rw [if_pos he, hT, ht, hs, hb, hr]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  · rw [if_neg hne, hT, ht, hs, hb, hr]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The slip of the standard field at the child's shortShift is `F y − F (y + (2ε_u D_u, 2ε_u N_u))`. -/
theorem slip_eq_shortShift (U : ChildFrame) (F : Field) (y : Site) :
    U.slip F 1 y = F y - F (y + (2 * U.eps * U.parents.odd.den, 2 * U.eps * U.parents.odd.num)) := by
  unfold ChildFrame.slip ChildFrame.shortShift
  rw [one_smul]

/-- The determinant of the earlier parents: `N_u (D + N) − D_u (D − N) = ε_u`. -/
theorem det_conj (U : ChildFrame) (N D : ℤ) (hb : U.child.num = D - N) (hr : U.child.den = D + N) :
    U.parents.odd.num * (D + N) - U.parents.odd.den * (D - N) = U.eps := by
  have hcn : U.child.num = 2 * U.parents.odd.num + U.parents.even.num := by
    unfold ChildFrame.child Parents.current Parents.combine
    ring
  have hcd : U.child.den = 2 * U.parents.odd.den + U.parents.even.den := by
    unfold ChildFrame.child Parents.current Parents.combine
    ring
  have he : U.eps = U.parents.odd.num * U.parents.even.den - U.parents.even.num * U.parents.odd.den := by
    unfold ChildFrame.eps Fraction.det
    ring
  rw [he, ← hb, ← hr, hcn, hcd]
  ring

end ZoneI1

end FLatticePaper.Induction
