import FLatticePaper.Plane.Induction.ChainDeck
import FLatticePaper.Plane.Induction.NativeCongruence
import FLatticePaper.Plane.Induction.Reflection
import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! Task 72 / Q29, item 7 of the raw-cut audit: the minus slip at the last V site.

The last V site is `vLast = I + V` with `I = (1, −1)` and `V` the transverse deck vector (`vLast` = `(n − d + 1, n + d − 1)`).
The grade of `I` is `L = n + d`, and the grades of `I` and `I + η σ` (`t(η σ) = −2η`) lie in the zero strip `[1 − d, n + 2d − 1]`
for `η = ±1`, `d ≥ 3`. So `slip F η I = 0`, and the transverse drift adds `2η`: `slip F η vLast = 2η`. At `η = −1` this is `−2`. -/

namespace FLatticePaper.FinalRootSlip

open FLatticePaper FLatticePaper.Induction

/-- The last V site as the translate `I + transverse` of `I = (1, −1)`. -/
theorem vLast_eq_I_add_transverse (frame : ChildFrame) :
    frame.vLast = (1, -1) + frame.child.modifiedDeck.transverse := by
  have ht : frame.child.modifiedDeck.transverse = frame.child.modifiedDeck.combine 0 1 := by
    unfold Farey.PeriodDeck.combine
    simp
  rw [ht, ChainDeck.combine_eq_vec]
  unfold ChildFrame.vLast
  ext <;> simp <;> ring

/-- The grade of `I = (1, −1)` is `n + d`. -/
theorem tGrade_I (frame : ChildFrame) : frame.tGrade (1, -1) = frame.child.num + frame.child.den := by
  unfold ChildFrame.tGrade
  ring

/-- **The slip at `I` vanishes for `η = ±1`**: both `I` and `I + η σ` lie in the zero strip. -/
theorem slip_I_eq_zero (frame : ChildFrame) {F : Field} (hP : frame.Packet F) {η : ℤ}
    (hη : η = 1 ∨ η = -1) : frame.slip F η (1, -1) = 0 := by
  obtain ⟨hn, hnd, -, hd3, -⟩ := frame.child_facts
  have hS := hP.strips.1
  have z0 : F (1, -1) = 0 := hS _ (by rw [tGrade_I]; omega) (by rw [tGrade_I]; omega)
  have hg : frame.tGrade ((1, -1) + η • frame.shortShift) = frame.child.num + frame.child.den - 2 * η := by
    rw [frame.tGrade_add_pt, NativeCongruence.tGrade_shortShift_smul, tGrade_I]
    ring
  have zη : F ((1, -1) + η • frame.shortShift) = 0 := by
    apply hS
    · rw [hg]
      rcases hη with rfl | rfl <;> omega
    · rw [hg]
      rcases hη with rfl | rfl <;> omega
  unfold ChildFrame.slip
  rw [z0, zη]
  ring

/-- **The minus slip at the last V site:** `D_η(vLast) = 2η`, so `D_{−1}(vLast) = −2`. -/
theorem slip_vLast (frame : ChildFrame) {F : Field} (hP : frame.Packet F) {η : ℤ}
    (hη : η = 1 ∨ η = -1) : frame.slip F η frame.vLast = 2 * η := by
  rw [vLast_eq_I_add_transverse, frame.slip_transverse F hP.periods η (1, -1), slip_I_eq_zero frame hP hη]
  ring

end FLatticePaper.FinalRootSlip
