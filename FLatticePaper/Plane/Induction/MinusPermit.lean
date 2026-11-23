import FLatticePaper.Plane.Induction.CanonicalSigned
import FLatticePaper.Plane.Induction.BothFreeGrades

/-! Task 72 / Q13 (the minus permit), the H-band part.

The minus raw slip is `D₋(w) = F w − F (w − σ)`. At a free H site the minus prescription (`prescribedH (−1)`) is east at even
sites and north at odd sites. The zero strip of `HasStrips` (`F = 0` on the grades `t ∈ [1 − d, n + 2d − 1]`) covers the four sites
`z`, `z + ε`, `z − σ`, `z + ε − σ` (`ε` the prescribed unit direction), so the slip increment is `0` and the permit holds. -/

namespace FLatticePaper.MinusPermit

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.CollarTop FLatticePaper.BothFreeGrades
  FLatticePaper.CollarBottomCases

/-- The minus prescription at a free H site: east at even sites, north at odd sites. -/
theorem prescribedH_minus_eq (frame : ChildFrame) (z : Site) :
    frame.prescribedH (-1) z = if EvenSite z then (1, 0) else (0, 1) := by
  unfold ChildFrame.prescribedH
  by_cases h1 : z = hFirst
  · rw [if_pos h1]
    have ho : ¬ EvenSite z := by rw [h1]; exact not_even_hFirst
    rw [if_neg ho]
    norm_num
  by_cases h2 : z = frame.hLast
  · have ho : ¬ EvenSite z := by rw [h2]; exact not_even_hLast frame
    rw [if_neg h1, if_pos h2, if_neg ho]
  rw [if_neg h1, if_neg h2]

theorem tGrade_add_east' (frame : ChildFrame) (z : Site) :
    frame.tGrade (z + (1, 0)) = frame.tGrade z + frame.child.num := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

theorem tGrade_add_north' (frame : ChildFrame) (z : Site) :
    frame.tGrade (z + (0, 1)) = frame.tGrade z - frame.child.den := by
  unfold ChildFrame.tGrade
  simp only [Prod.fst_add, Prod.snd_add]
  ring

/-- The minus shift `z + (−1)•σ` moves the grade by `+2`. -/
theorem tGrade_add_minus_shift (frame : ChildFrame) (z : Site) :
    frame.tGrade (z + (-1 : ℤ) • frame.shortShift) = frame.tGrade z + 2 := by
  have e : (-1 : ℤ) • frame.shortShift = ((-1 : ℤ) * frame.shortShift.1, (-1 : ℤ) * frame.shortShift.2) := by
    ext <;> simp
  rw [e, frame.tGrade_add_shift]
  ring

/-- **The H-band minus permit.** At a free H site the minus prescription is permitted for the raw slip `D₋`:
`slipPermits F (w ↦ F(w + (−1)•σ)) z (z + prescribedH (−1) z)`. The zero strip of `HasStrips` carries the four values. -/
theorem minus_permit_H (frame : ChildFrame) (F : Field) (hS : frame.HasStrips F) {z : Site}
    (hz : z ∈ frame.freeH) :
    slipPermits F (fun w => F (w + (-1 : ℤ) • frame.shortShift)) z (z + frame.prescribedH (-1) z) := by
  obtain ⟨-, -, hsp⟩ := hz
  obtain ⟨hn0, hnd1, hd2, -, -⟩ := frame.child_facts
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨hnodd, hdodd⟩ := frame.child_odd
  have hzero : ∀ w, 1 - frame.child.den ≤ frame.tGrade w → frame.tGrade w ≤ frame.child.num + 2 * frame.child.den - 1 →
      F w = 0 := fun w h1 h2 => hS.1 w h1 h2
  have hpar := t_parity frame.child.num frame.child.den z.1 z.2 hnodd hdodd
  unfold ChildFrame.hSpectrum at hsp
  rw [prescribedH_minus_eq]
  unfold slipPermits slipIncrement
  have hpar' : frame.tGrade z % 2 = (z.1 + z.2) % 2 := hpar
  by_cases he : EvenSite z
  · rw [if_pos he]
    have hpz : (z.1 + z.2) % 2 = 0 := he
    have hb0 : 1 - frame.child.den ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1 := by
      omega
    have hF1 : F z = 0 := hzero z hb0.1 hb0.2
    have hF2 : F (z + (-1 : ℤ) • frame.shortShift) = 0 :=
      hzero _ (by rw [tGrade_add_minus_shift]; omega) (by rw [tGrade_add_minus_shift]; omega)
    have hF3 : F (z + (1, 0)) = 0 :=
      hzero _ (by rw [tGrade_add_east']; omega) (by rw [tGrade_add_east']; omega)
    have hF4 : F (z + (1, 0) + (-1 : ℤ) • frame.shortShift) = 0 :=
      hzero _ (by rw [tGrade_add_minus_shift, tGrade_add_east']; omega)
        (by rw [tGrade_add_minus_shift, tGrade_add_east']; omega)
    simp only [hF1, hF2, hF3, hF4]
    norm_num
  · rw [if_neg he]
    have hpz : ¬ (z.1 + z.2) % 2 = 0 := he
    have hb0 : 1 - frame.child.den ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.num + 2 * frame.child.den - 1 := by
      omega
    have hF1 : F z = 0 := hzero z hb0.1 hb0.2
    have hF2 : F (z + (-1 : ℤ) • frame.shortShift) = 0 :=
      hzero _ (by rw [tGrade_add_minus_shift]; omega) (by rw [tGrade_add_minus_shift]; omega)
    have hF3 : F (z + (0, 1)) = 0 :=
      hzero _ (by rw [tGrade_add_north']; omega) (by rw [tGrade_add_north']; omega)
    have hF4 : F (z + (0, 1) + (-1 : ℤ) • frame.shortShift) = 0 :=
      hzero _ (by rw [tGrade_add_minus_shift, tGrade_add_north']; omega)
        (by rw [tGrade_add_minus_shift, tGrade_add_north']; omega)
    simp only [hF1, hF2, hF3, hF4]
    norm_num

end FLatticePaper.MinusPermit
