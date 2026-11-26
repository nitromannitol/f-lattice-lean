import FLatticePaper.Plane.Induction.RouteH3
import FLatticePaper.Plane.Induction.WestForced
import FLatticePaper.Plane.Induction.RouteSteps
import FLatticePaper.Plane.Induction.FanInputs
import FLatticePaper.Plane.Induction.ShortPassages
import FLatticePaper.Plane.Induction.FreeNonfree

/-! # The middle source of the `h3` second arrow is strictly interior

For an even free H root `z ≠ (2,0)` whose west neighbour `b = (z.1 − 1, z.2)` is a free H root, the north neighbour
`m = (z.1 − 1, z.2 + 1)` is strictly interior. With `t(b) ≥ n + 2` (the odd spectrum, `b ≠ hFirst`), `s(b) > 3d + n − 2`
(`WestForced.sGrade_odd_H_big`, `b ≠ hLast`), and `s(z) < T + 2 − 2d` (`RouteSteps.freeH_even_s_lt`):
`t(m) = t(z) − n − d ∈ (d + n − 2 − T, 2)` and `s(m) = s(z) − 2n ∈ (2n, T)`. -/

namespace FLatticePaper.HMidStrict

open FLatticePaper FLatticePaper.Induction FLatticePaper.W1

theorem m_strict (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z)
    (hz2 : z ≠ (2, 0)) (hq : (z.1 - 1, z.2) ∈ frame.freeH) :
    StrictInterior frame.child.num frame.child.den (z.1 - 1, z.2 + 1) := by
  obtain ⟨hn0, hnd, hd2, -, -⟩ := frame.child_facts
  obtain ⟨-, hdO⟩ := frame.child_odd
  have hbig := FLatticePaper.FreeNonfree.big_T (frame := frame)
  have hTd : frame.child.periodDenominator
      = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num - frame.child.num ^ 2 := rfl
  have hodd : ¬ EvenSite (z.1 - 1, z.2) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  -- the west neighbour: odd, t(b) odd and ≥ n, t(b) ≠ n, so t(b) ≥ n + 2
  have hbpar : frame.tGrade (z.1 - 1, z.2) % 2 = 1 := FLatticePaper.Induction.ShortPassages.tGrade_parity' frame _ hodd
  have hbne : frame.tGrade (z.1 - 1, z.2) ≠ frame.child.num := by
    intro ht
    apply hz2
    have hb := FLatticePaper.FanInputs.freeH_odd_t_num frame hq hodd ht
    have h1 : (z.1 - 1, z.2).1 = FLatticePaper.Induction.hFirst.1 := by rw [hb]
    have h2 : (z.1 - 1, z.2).2 = FLatticePaper.Induction.hFirst.2 := by rw [hb]
    unfold FLatticePaper.Induction.hFirst at h1 h2
    dsimp only at h1 h2
    exact Prod.ext (by omega) (by omega)
  have hbsp : frame.child.num ≤ frame.tGrade (z.1 - 1, z.2) := by
    have hq' := hq
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hq'
    unfold ChildFrame.hSpectrum at hq'
    rcases hq'.2.2 with h | h <;> omega
  have hnodd : frame.child.num % 2 = 1 := FLatticePaper.FanInputs.num_odd frame
  have hbt : frame.child.num + 2 ≤ frame.tGrade (z.1 - 1, z.2) := by omega
  -- the west neighbour is not the last site: its grade would make `t(z) = d + n`
  have hbne_last : (z.1 - 1, z.2) ≠ frame.hLast := by
    intro h
    have h1 : z.1 - 1 = frame.child.den := by
      have := congrArg Prod.fst h
      simpa [ChildFrame.hLast] using this
    have h2 : z.2 = frame.child.num - 1 := by
      have := congrArg Prod.snd h
      simpa [ChildFrame.hLast] using this
    have htz : frame.tGrade z = frame.child.num + frame.child.den := by
      unfold ChildFrame.tGrade
      rw [show z.1 = frame.child.den + 1 by omega, h2]
      ring
    have hz' := hz
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz'
    unfold ChildFrame.hSpectrum at hz'
    have hzE := hev
    rcases hz'.2.2 with h' | h' <;> omega
  have hsb := FLatticePaper.WestForced.sGrade_odd_H_big hq hodd hbne_last hbt
  have hsup := FLatticePaper.Induction.RouteSteps.freeH_even_s_lt frame (x := z.1) (y := z.2) hz hev
  have hzsp : frame.child.num + 2 * frame.child.den - 2 ≥ frame.child.num := by omega
  have hz' := hz
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz'
  have hzpar : frame.tGrade z % 2 = 0 := by
    rw [FLatticePaper.Induction.tGrade_parity frame z]
    exact hev
  have hzt : 2 ≤ frame.tGrade z ∧ frame.tGrade z ≤ frame.child.den + frame.child.num - 2 := by
    have hz'' := hz'
    unfold ChildFrame.hSpectrum at hz''
    rcases hz''.2.2 with h | h
    · exact ⟨by omega, by omega⟩
    · omega
  have hm_even : EvenSite (z.1 - 1, z.2 + 1) := by
    unfold EvenSite at hev ⊢
    simp only at hev ⊢
    omega
  have e0 : frame.tGrade (z.1 - 1, z.2) = frame.tGrade z - frame.child.num := by
    unfold ChildFrame.tGrade; ring
  have e0s : frame.sGrade (z.1 - 1, z.2) = frame.sGrade z - (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade; ring
  have e1 : w1t frame.child.num frame.child.den (z.1 - 1, z.2 + 1)
      = frame.tGrade z - frame.child.num - frame.child.den := by
    unfold w1t ChildFrame.tGrade; ring
  have e2 : w1s frame.child.num frame.child.den (z.1 - 1, z.2 + 1)
      = frame.sGrade z - 2 * frame.child.num := by
    unfold w1s ChildFrame.sGrade; ring
  have hTw : w1T frame.child.num frame.child.den = frame.child.periodDenominator := hTd.symm
  unfold StrictInterior
  simp only [w1b, w1a, w1h, w1c, if_pos hm_even]
  rw [e1, e2, hTw]
  rw [e0] at hbt
  rw [e0s] at hsb
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end FLatticePaper.HMidStrict
