import FLatticePaper.Plane.Induction.FirstOfferGrade
import FLatticePaper.Plane.Induction.FreeHPrice
import FLatticePaper.Plane.Induction.FreeTraceBox

/-! The parent-grade window of the prescribed neighbour in phase one (`ε = +1`).

With `N d − n D = 1` (`hrel`), the parent grade `T_p(z) = N z₁ − D z₂` and the child grade `t(z) = n z₁ − d z₂` determine `z`
(`z₂ = n·T_p − N·t`, `z₁ = d·T_p − D·t`). For an odd free H root `r` the child grade lies in `[n, d]`, and `T_p(r) = 1` forces
`r = (1,0) = H_0`; so `T_p(r) ∈ [2, D+1]` for `r ≠ H_0`. For an even root `T_p(r) ∈ [1−2N, D+N]`. The prescribed neighbour has
`T_p(r + (1,0)) = T_p(r) + N` (even `r`) and `T_p(r + (0,1)) = T_p(r) − D` (odd `r ≠ H_0`); both lie in `[2−D, N+2D]`. -/

namespace FLatticePaper.PhaseOneWindow

open Farey FLatticePaper FLatticePaper.Induction

/-- **Odd roots with parent grade `1` are `H_0`.** -/
theorem lattice_one_odd (n d N D x1 x2 t : ℤ) (hrel : N * d - n * D = 1)
    (ht : t = n * x1 - d * x2) (hT : N * x1 - D * x2 = 1) :
    x1 = d - D * t ∧ x2 = n - N * t := by
  constructor
  · linear_combination D * ht + d * hT + (-x1) * hrel
  · linear_combination N * ht + n * hT + (-x2) * hrel

theorem lattice_hFirst (n d N D x1 x2 t : ℤ) (hn0 : 0 < n) (hN1 : 1 ≤ N) (hrel : N * d - n * D = 1)
    (ht : t = n * x1 - d * x2) (hx2 : 0 ≤ x2) (htn : n ≤ t) (htd : t ≤ d) (hT : N * x1 - D * x2 = 1) :
    x1 = 1 ∧ x2 = 0 := by
  obtain ⟨e1, e2⟩ := lattice_one_odd n d N D x1 x2 t hrel ht hT
  have hN : N = 1 := by nlinarith
  subst hN
  constructor
  · nlinarith
  · nlinarith

/-- **The prescribed neighbour's parent grade, phase one.** For a free H root `r ≠ H_0` with `N d − n D = 1`, the neighbour
`i = r + prescribedH η r` has `T_p(i) ∈ [2−D, N+2D]`. -/
theorem tp_neighbour_window (frame : ChildFrame) (hN1 : 1 ≤ frame.parents.odd.num)
    (hND : frame.parents.odd.num < frame.parents.odd.den)
    (hrel : frame.parents.odd.num * frame.child.den - frame.child.num * frame.parents.odd.den = 1)
    {r : Site} (hr : r ∈ frame.freeH) (hr1 : r ≠ hFirst) (η : ℤ) :
    2 - frame.parents.odd.den ≤ frame.parents.odd.num * (r + frame.prescribedH η r).1 -
        frame.parents.odd.den * (r + frame.prescribedH η r).2 ∧
      frame.parents.odd.num * (r + frame.prescribedH η r).1 - frame.parents.odd.den * (r + frame.prescribedH η r).2 ≤
        frame.parents.odd.num + 2 * frame.parents.odd.den := by
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  obtain ⟨hb1, hb2, hb3, hb4⟩ := FLatticePaper.Induction.FreeTraceBox.freeH_box frame hr
  have hsp := hr.2.2
  unfold ChildFrame.hSpectrum at hsp
  have hpar : frame.tGrade r % 2 = (r.1 + r.2) % 2 := by
    unfold ChildFrame.tGrade
    rw [Int.sub_emod, Int.mul_emod, Int.mul_emod frame.child.den, hco1, hco2]
    omega
  by_cases hev : EvenSite r
  · unfold EvenSite at hev
    rw [FLatticePaper.FreePolicy.pH_even frame η (by unfold EvenSite; exact hev)]
    have ht_e : 2 ≤ frame.tGrade r ∧ frame.tGrade r ≤ frame.child.den + frame.child.num - 2 := by
      rcases hsp with ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ <;> omega
    obtain ⟨tp1, tp2⟩ := FLatticePaper.FirstOfferGrade.tp_even frame.child.num frame.child.den
      frame.parents.odd.num frame.parents.odd.den r.1 r.2 (frame.tGrade r) (by omega) hN1 hrel rfl hb3 hb4
      ht_e.1 ht_e.2
    simp only [Prod.fst_add, Prod.snd_add]
    constructor <;> nlinarith
  · unfold EvenSite at hev
    rw [FLatticePaper.FreePolicy.pH_odd' frame η (by unfold EvenSite; exact hev) hr1]
    have ht_o : frame.child.num ≤ frame.tGrade r ∧ frame.tGrade r ≤ frame.child.den := by
      rcases hsp with ⟨h1', h2, h3⟩ | ⟨h1', h2, h3⟩ <;> omega
    obtain ⟨tp1, tp2⟩ := FLatticePaper.FirstOfferGrade.tp_odd frame.child.num frame.child.den
      frame.parents.odd.num frame.parents.odd.den r.1 r.2 (frame.tGrade r) (by omega) hN1 hrel rfl hb3 hb4
      ht_o.1 ht_o.2
    have hne1 : frame.parents.odd.num * r.1 - frame.parents.odd.den * r.2 ≠ 1 := by
      intro hT1
      apply hr1
      obtain ⟨e1, e2⟩ := lattice_hFirst frame.child.num frame.child.den frame.parents.odd.num
        frame.parents.odd.den r.1 r.2 (frame.tGrade r) (by omega) hN1 hrel rfl hb3 ht_o.1 ht_o.2 hT1
      ext
      · simp [FLatticePaper.Induction.hFirst, e1]
      · simp [FLatticePaper.Induction.hFirst, e2]
    have tp1' : 2 ≤ frame.parents.odd.num * r.1 - frame.parents.odd.den * r.2 := by omega
    simp only [Prod.fst_add, Prod.snd_add]
    constructor <;> nlinarith

end FLatticePaper.PhaseOneWindow
