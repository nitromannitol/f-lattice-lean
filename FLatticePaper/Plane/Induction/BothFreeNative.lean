import FLatticePaper.Plane.Induction.BothFreeRise
import FLatticePaper.Plane.Induction.NativeCases
import FLatticePaper.Plane.Induction.NativeCongruence
import FLatticePaper.Plane.Induction.CanonicalSigned

/-! Task 72 / Q28: the both-free exclusion with one native free representative per root (`Q28.md`, reading (a)). The two roots are native
points `w0` (for `z`) and `w1` (for `z + ησ`), each free (H or V) after its own deck translation. The sign-η policy `P` chooses `w0 + h` at
`w0`; the sign-(−η) policy `Q` chooses `w1 − h` at `w1`; the primitive price rises by one along `w1 → w1 + h`; and the congruence of the two
grades holds (`NativeCongruence.t_congruence`). Case 1 (`w1` on V): the price is constant on the star of `w1` (`price_const_of_window`), so the
rise is impossible. Cases 2 and 3 (`w1` on H): `NativeCases.native_HH_false` and `native_VH_false`. -/

namespace FLatticePaper.BothFreeNative

open FLatticePaper FLatticePaper.Induction FLatticePaper.BothFreeRise

theorem both_free_rise_native (frame : ChildFrame) {F : Field} (hS : frame.HasStrips F) {η : ℤ}
    (hη : η = 1 ∨ η = -1) (hc : 3 ≤ frame.child.den - frame.child.num)
    {P Q : Site → Site → Prop} (hP : PrescribedAt frame F η P) (hQ : PrescribedAt frame F (-η) Q)
    {w0 w1 h : Site} (i0 j0 i1 j1 : ℤ)
    (hw0 : w0 ∈ frame.freeH ∨ w0 ∈ frame.freeV) (hw1 : w1 ∈ frame.freeH ∨ w1 ∈ frame.freeV)
    (hwF0 : laplacian F w0 = 0) (hwG1 : laplacian F w1 = 0)
    (hPw : P w0 (w0 + h)) (hQw : Q w1 (w1 - h))
    (hu' : w1 + h = incomingNeg w1 ∨ w1 + h = incomingPos w1)
    (hrise : frame.price F (w1 + h) = frame.price F w1 + 1)
    (hcong : w1 = w0 + η • frame.shortShift + frame.child.modifiedDeck.combine i0 j0 -
      frame.child.modifiedDeck.combine i1 j1)
    (hpar : EvenSite w0 ↔ EvenSite w1) : False := by
  by_cases hw1V : w1 ∈ frame.freeV
  · -- case 1: the price is constant on the input star of a free V centre
    have hz := window_centre_of_freeV frame hw1V
    have hu := window_input_of_freeV frame hc hw1V hu'
    have := price_const_of_window frame F hS hz hu
    omega
  · have hw1H : w1 ∈ frame.freeH := hw1.resolve_right hw1V
    have hk := NativeCongruence.t_congruence frame w0 w1 η i0 j0 i1 j1 hcong
    by_cases hw0H : w0 ∈ frame.freeH
    · -- case 2: both H
      have hh : h = frame.prescribedH η w0 := by
        have e := (hP.1 w0 hw0H hwF0 (w0 + h)).mp hPw
        exact add_left_cancel e
      have hq : frame.prescribedH (-η) w1 = -h := by
        have e := (hQ.1 w1 hw1H hwG1 (w1 - h)).mp hQw
        have e2 : w1 - h = w1 + frame.prescribedH (-η) w1 := e
        have e3 : w1 + frame.prescribedH (-η) w1 = w1 - h := e2.symm
        have e4 : frame.prescribedH (-η) w1 = -h := by
          have := congrArg (fun x => x - w1) e3
          simpa [sub_eq_add_neg, add_comm, add_left_comm] using this
        exact e4
      exact NativeCases.native_HH_false frame hη hw0H hw1H hpar _ hk (by rw [hq, hh])
    · -- case 3: w0 on V, w1 on H
      have hw0V : w0 ∈ frame.freeV := hw0.resolve_left hw0H
      have hh : h = frame.prescribedV η w0 := by
        have e := (hP.2 w0 hw0V hwF0 (w0 + h)).mp hPw
        exact add_left_cancel e
      have hq : frame.prescribedH (-η) w1 = -h := by
        have e := (hQ.1 w1 hw1H hwG1 (w1 - h)).mp hQw
        have e2 : w1 - h = w1 + frame.prescribedH (-η) w1 := e
        have e3 : w1 + frame.prescribedH (-η) w1 = w1 - h := e2.symm
        have e4 : frame.prescribedH (-η) w1 = -h := by
          have := congrArg (fun x => x - w1) e3
          simpa [sub_eq_add_neg, add_comm, add_left_comm] using this
        exact e4
      exact NativeCases.native_VH_false frame hη hw0V hw1H hpar _ hk (by rw [hq, hh])

end FLatticePaper.BothFreeNative
