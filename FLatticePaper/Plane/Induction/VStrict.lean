import FLatticePaper.Plane.Induction.VLattice
import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.S3FreeBoundary

/-! # Strict interior of the V middles of the `v3` row (grade lemmas)

For an odd free V root `z` (closed polygon, V-spectrum of `s(z)`):
* `η = +1`: the middle `z + (1, 1)` is strictly interior (`vplus_middle_strict`), from `VLattice.lower_t`, `VLattice.lt_top`;
* `η = −1`: the translate `(z − (1, 1)) + (d, n)` is strictly interior (`vminus_middle_strict`), from `VLattice.gt_n_sub_T`,
  `VLattice.lt_2n_sub_d`. -/

namespace FLatticePaper.VStrict

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1

/-- The grade facts of an odd free V root. -/
theorem odd_free_V_facts {frame : ChildFrame} {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) :
    frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den ∧
      2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2 ∧
      (0 ≤ frame.sGrade z ∧ frame.sGrade z ≤ 2 * frame.child.num ∨
        2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
          frame.sGrade z ≤ frame.child.den + frame.child.num - 2) := by
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hz
  obtain ⟨hzcl, -, hzvs⟩ := hz
  have hcl := (frame.mem_closedPolygon_iff z).mp hzcl
  have hodd_cl : ¬ EvenSite z ∧ frame.child.num - frame.child.periodDenominator ≤ frame.tGrade z ∧
      frame.tGrade z ≤ frame.child.den ∧ 2 - frame.child.den + frame.child.num ≤ frame.sGrade z ∧
      frame.sGrade z ≤ frame.child.periodDenominator + frame.child.den + frame.child.num - 2 := by
    rcases hcl with h | h
    · exact absurd h.1 hodd
    · exact h
  unfold ChildFrame.vSpectrum at hzvs
  obtain ⟨-, hvs⟩ := hzvs
  exact ⟨hodd_cl.2.1, hodd_cl.2.2.1, hodd_cl.2.2.2.1, hodd_cl.2.2.2.2, hvs⟩

/-- The middle `z + (1, 1)` of the `η = +1` V row is strictly interior (`t = t(z) + n − d`, `s = s(z) + 2d`). -/
theorem vplus_middle_strict {frame : ChildFrame} {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) :
    StrictInterior frame.child.num frame.child.den (z.1 + 1, z.2 + 1) := by
  obtain ⟨hn0, -, hd2, -, hT⟩ := frame.child_facts
  have hn1 : 1 ≤ frame.child.num := by omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨h1, h2, h3, h4, hvs⟩ := odd_free_V_facts hz hodd
  have hodd' : (z.1 + z.2) % 2 = 1 := by
    have h : ¬ ((z.1 + z.2) % 2 = 0) := hodd
    omega
  obtain ⟨hs_lo, hs_hi⟩ := VLattice.s_range hnd hvs
  have hsz : frame.sGrade z = (frame.child.den + frame.child.num) * z.1 + (frame.child.den - frame.child.num) * z.2 := rfl
  have htz : frame.tGrade z = frame.child.num * z.1 - frame.child.den * z.2 := rfl
  have hlow := VLattice.lower_t hn1 hnd hodd' htz.symm hsz.symm (by rw [hT] at h1; exact h1) hs_lo hs_hi
  have hup := VLattice.lt_top hn1 hnd htz.symm hsz.symm h2 hs_lo hs_hi
  have hTbig : 4 * frame.child.den - 4 < frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  have hodd_p : ¬ EvenSite (z.1 + 1, z.2 + 1) := by
    intro h
    have h' : (z.1 + 1 + (z.2 + 1)) % 2 = 0 := h
    omega
  have htw : FLatticePaper.W1.w1t frame.child.num frame.child.den (z.1 + 1, z.2 + 1)
      = frame.tGrade z + frame.child.num - frame.child.den := by
    unfold FLatticePaper.W1.w1t ChildFrame.tGrade
    ring
  have hsw : FLatticePaper.W1.w1s frame.child.num frame.child.den (z.1 + 1, z.2 + 1)
      = frame.sGrade z + 2 * frame.child.den := by
    unfold FLatticePaper.W1.w1s ChildFrame.sGrade
    ring
  have hTw : FLatticePaper.W1.w1T frame.child.num frame.child.den = frame.child.periodDenominator := hT.symm
  unfold StrictInterior
  simp only [FLatticePaper.W1.w1b, FLatticePaper.W1.w1a, FLatticePaper.W1.w1h, FLatticePaper.W1.w1c, if_neg hodd_p]
  rw [htw, hsw, hTw]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hlow, hup, hs_lo, hs_hi, hTbig]

/-- The translate `(z − (1, 1)) + (d, n)` of the `η = −1` middle `z − (1, 1)` of the V row is strictly interior
(`t = t(z) + d − n`, `s = s(z) − 2d + T`). -/
theorem vminus_middle_strict {frame : ChildFrame} {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z) :
    StrictInterior frame.child.num frame.child.den ((z.1 - 1, z.2 - 1) + (frame.child.den, frame.child.num)) := by
  obtain ⟨hn0, -, hd2, -, hT⟩ := frame.child_facts
  have hn1 : 1 ≤ frame.child.num := by omega
  have hnd : frame.child.num + 2 ≤ frame.child.den := by omega
  obtain ⟨h1, h2, h3, h4, hvs⟩ := odd_free_V_facts hz hodd
  have hodd' : (z.1 + z.2) % 2 = 1 := by
    have h : ¬ ((z.1 + z.2) % 2 = 0) := hodd
    omega
  obtain ⟨hs_lo, hs_hi⟩ := VLattice.s_range hnd hvs
  have hsz : frame.sGrade z = (frame.child.den + frame.child.num) * z.1 + (frame.child.den - frame.child.num) * z.2 := rfl
  have htz : frame.tGrade z = frame.child.num * z.1 - frame.child.den * z.2 := rfl
  have hlo := VLattice.gt_n_sub_T hn1 hnd htz.symm hsz.symm (by rw [hT] at h1; exact h1) hs_lo hs_hi
  have hup := VLattice.lt_2n_sub_d hn1 hnd hodd' htz.symm hsz.symm h2 hs_lo hs_hi
  have hTbig : 4 * frame.child.den - 4 < frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  have hodd_p : ¬ EvenSite ((z.1 - 1, z.2 - 1) + (frame.child.den, frame.child.num)) := by
    intro h
    have h' : (z.1 - 1 + frame.child.den + (z.2 - 1 + frame.child.num)) % 2 = 0 := h
    have hpar : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
    omega
  have htw : FLatticePaper.W1.w1t frame.child.num frame.child.den
      ((z.1 - 1, z.2 - 1) + (frame.child.den, frame.child.num)) = frame.tGrade z - frame.child.num + frame.child.den := by
    unfold FLatticePaper.W1.w1t ChildFrame.tGrade
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hsw : FLatticePaper.W1.w1s frame.child.num frame.child.den
      ((z.1 - 1, z.2 - 1) + (frame.child.den, frame.child.num))
      = frame.sGrade z - 2 * frame.child.den + frame.child.periodDenominator := by
    unfold FLatticePaper.W1.w1s ChildFrame.sGrade
    rw [hT]
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  have hTw : FLatticePaper.W1.w1T frame.child.num frame.child.den = frame.child.periodDenominator := hT.symm
  unfold StrictInterior
  simp only [FLatticePaper.W1.w1b, FLatticePaper.W1.w1a, FLatticePaper.W1.w1h, FLatticePaper.W1.w1c, if_neg hodd_p]
  rw [htw, hsw, hTw]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hlo, hup, hs_lo, hs_hi, hTbig, h2, h4]

end FLatticePaper.VStrict
