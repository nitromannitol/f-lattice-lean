import FLatticePaper.Plane.Induction.FreePolicy
import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.Potentials
import FLatticePaper.Plane.Induction.Binary
import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! The free-edge slip permit at the H arc, zero-strip form.

The slip `D_η(z) = F z − F(z + η•s)` (`ChildFrame.slip`, with `s = shortShift`) has `t(s) = tGrade s = −2`. At a free H root `x` and
its prescribed neighbour `y = x + prescribedH η x`, the four points `x`, `x + η s`, `y`, `y + η s` all have child t-grade inside the zero
window `[1 − d, n + 2d − 1]` of the field, so `F` vanishes there and `D_η(x) = D_η(y) = 0`. -/

namespace FLatticePaper.SlipPermitH

open Farey FLatticePaper FLatticePaper.Induction

theorem tGrade_shortShift (frame : ChildFrame) : frame.tGrade frame.shortShift = -2 := by
  have he := frame.eps_eq
  rcases frame.eps_unit with h | h
  · rw [h] at he
    unfold ChildFrame.tGrade ChildFrame.shortShift
    rw [h]
    linear_combination 2 * he
  · rw [h] at he
    unfold ChildFrame.tGrade ChildFrame.shortShift
    rw [h]
    linear_combination (-2) * he

theorem tGrade_add (frame : ChildFrame) (a b : Site) : frame.tGrade (a + b) = frame.tGrade a + frame.tGrade b := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem tGrade_smul (frame : ChildFrame) (k : ℤ) (a : Site) : frame.tGrade (k • a) = k * frame.tGrade a := by
  unfold ChildFrame.tGrade
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The shifted point `η • s` has t-grade `−2η`. -/
theorem tGrade_eta_shortShift (frame : ChildFrame) (η : ℤ) :
    frame.tGrade (η • frame.shortShift) = -2 * η := by
  rw [tGrade_smul, tGrade_shortShift]
  ring

/-- The zero strip of the field: the t-window `[1 − d, n + 2d − 1]` is where `F` vanishes. -/
theorem zero_of_window {frame : ChildFrame} {F : Field} (hS : frame.HasStrips F) {z : Site}
    (h1 : 1 - frame.child.den ≤ frame.tGrade z) (h2 : frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1) :
    F z = 0 :=
  hS.1 z h1 h2

/-- The zero strip at a pair `y`, `y + η•s`, with the t-grades `ty` and `ty − 2η`. -/
theorem zero_pair {frame : ChildFrame} {F : Field} (hS : frame.HasStrips F) (η : ℤ) {y : Site} {ty : ℤ}
    (hty : frame.tGrade y = ty)
    (hb : 1 - frame.child.den ≤ ty ∧ ty ≤ frame.child.num + 2 * frame.child.den - 1)
    (hb' : 1 - frame.child.den ≤ ty - 2 * η ∧ ty - 2 * η ≤ frame.child.num + 2 * frame.child.den - 1) :
    F y = 0 ∧ F (y + η • frame.shortShift) = 0 := by
  constructor
  · exact zero_of_window hS (by rw [hty]; exact hb.1) (by rw [hty]; exact hb.2)
  · apply zero_of_window hS
    · rw [tGrade_add, tGrade_eta_shortShift frame η, hty]
      linarith [hb'.1]
    · rw [tGrade_add, tGrade_eta_shortShift frame η, hty]
      linarith [hb'.2]

theorem tGrade_parity (frame : ChildFrame) (z : Site) : frame.tGrade z % 2 = (z.1 + z.2) % 2 := by
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  unfold ChildFrame.tGrade
  rw [Int.sub_emod, Int.mul_emod, Int.mul_emod frame.child.den, hco1, hco2]
  omega

/-- **The slip vanishes at a free H root and at its prescribed neighbour.** -/
theorem slip_zero_root (frame : ChildFrame) {F : Field} (hS : frame.HasStrips F) {x : Site}
    (hx : x ∈ frame.freeH) (hn3 : 3 ≤ frame.child.num) {η : ℤ} (hη : η = 1 ∨ η = -1) :
    frame.slip F η x = 0 ∧ frame.slip F η (x + frame.prescribedH η x) = 0 := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  have hnd2 : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨hb1, hb2, hb3, hb4⟩ := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hx
  have hsp := hx.2.2
  unfold ChildFrame.hSpectrum at hsp
  have hpar := tGrade_parity frame x
  obtain ⟨u, hu⟩ : ∃ u, u = frame.tGrade x := ⟨_, rfl⟩
  rw [← hu] at hsp hpar
  have hxz := zero_pair hS η (y := x) (ty := u) hu.symm
    (by rcases hsp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega)
    (by rcases hsp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rcases hη with rfl | rfl <;> omega)
  constructor
  · unfold ChildFrame.slip
    rw [hxz.1, hxz.2]
    ring
  · by_cases hF : x = FLatticePaper.Induction.hFirst
    · subst hF
      rw [ChildFrame.prescribedH_hFirst]
      have hu' : frame.tGrade FLatticePaper.Induction.hFirst = frame.child.num := by
        unfold ChildFrame.tGrade FLatticePaper.Induction.hFirst
        ring
      have hty : frame.tGrade (FLatticePaper.Induction.hFirst + (0, -η)) = frame.child.num + η * frame.child.den := by
        rw [tGrade_add, hu']
        unfold ChildFrame.tGrade
        ring
      have hyz := zero_pair hS η (y := FLatticePaper.Induction.hFirst + (0, -η)) hty
        (by rcases hη with rfl | rfl <;> omega)
        (by rcases hη with rfl | rfl <;> omega)
      unfold ChildFrame.slip
      rw [hyz.1, hyz.2]
      ring
    · by_cases hev : EvenSite x
      · unfold EvenSite at hev
        rw [FLatticePaper.FreePolicy.pH_even frame η (by unfold EvenSite; exact hev)]
        have e1 : frame.tGrade (x + (1, 0)) = u + frame.child.num := by
          rw [tGrade_add, ← hu]
          unfold ChildFrame.tGrade
          ring
        have hyz := zero_pair hS η (y := x + (1, 0)) (ty := u + frame.child.num) e1
          (by rcases hsp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega)
          (by rcases hsp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rcases hη with rfl | rfl <;> omega)
        unfold ChildFrame.slip
        rw [hyz.1, hyz.2]
        ring
      · unfold EvenSite at hev
        rw [FLatticePaper.FreePolicy.pH_odd' frame η (by unfold EvenSite; exact hev) hF]
        have e1 : frame.tGrade (x + (0, 1)) = u - frame.child.den := by
          rw [tGrade_add, ← hu]
          unfold ChildFrame.tGrade
          ring
        have hyz := zero_pair hS η (y := x + (0, 1)) (ty := u - frame.child.den) e1
          (by rcases hsp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> omega)
          (by rcases hsp with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> rcases hη with rfl | rfl <;> omega)
        unfold ChildFrame.slip
        rw [hyz.1, hyz.2]
        ring

end FLatticePaper.SlipPermitH
