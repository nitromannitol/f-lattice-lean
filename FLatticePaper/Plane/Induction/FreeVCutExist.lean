import FLatticePaper.Plane.Induction.VOddLower
import FLatticePaper.Plane.Induction.HX2Diag
import FLatticePaper.Plane.Induction.FreeCutSucc
import FLatticePaper.Plane.Induction.VLastOfT
import FLatticePaper.Plane.Induction.FanInputs

/-! # The V successor exists off `vLast`

For `z ∈ freeV` with `z ≠ vLast`, one of `z + (0,1)` and `z + (-1,1)` lies in `freeV`. The grades of the candidates are
linear in the grades of `z`. Even sites take the even bounds (`root_bounds`, `t_le_neg_L`, `t_not_mid`, and `t ≠ L - P` from
`vLast_of_tGrade`); odd sites take the lower bound `odd_lower_of_mem`; `T` is even because `n` and `d` are odd. -/

namespace FLatticePaper.FreeVCutExist

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

theorem tGrade_eq_w1t (frame : ChildFrame) (z : Site) :
    frame.tGrade z = w1t frame.child.num frame.child.den z := rfl

theorem sGrade_eq_w1s (frame : ChildFrame) (z : Site) :
    frame.sGrade z = w1s frame.child.num frame.child.den z := rfl

theorem w1t_succY (n d x y : ℤ) : w1t n d (x, y + 1) = w1t n d (x, y) - d := by
  unfold w1t; ring
theorem w1s_succY (n d x y : ℤ) : w1s n d (x, y + 1) = w1s n d (x, y) + (d - n) := by
  unfold w1s; ring
theorem w1t_predX (n d x y : ℤ) : w1t n d (x - 1, y) = w1t n d (x, y) - n := by
  unfold w1t; ring
theorem w1s_predX (n d x y : ℤ) : w1s n d (x - 1, y) = w1s n d (x, y) - (d + n) := by
  unfold w1s; ring

/-- The V successor exists from an even site. -/
theorem freeV_succ_of_even (frame : ChildFrame) {x y : ℤ} (hz : (x, y) ∈ frame.freeV) (hp : (x + y) % 2 = 0)
    (hT2 : frame.child.periodDenominator % 2 = 0)
    (hlo : frame.child.den + frame.child.num - frame.child.periodDenominator ≤ frame.tGrade (x, y))
    (hs2 : frame.sGrade (x, y) ≤ 2 * frame.child.num)
    (hne : frame.tGrade (x, y) ≠ frame.child.den + frame.child.num - frame.child.periodDenominator)
    (htp : frame.tGrade (x, y) % 2 = 0) :
    (x, y + 1) ∈ frame.freeV ∨ (x - 1, y + 1) ∈ frame.freeV := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := frame.child_num_odd
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have e0 : EvenSite (x, y) := by unfold EvenSite; show (x + y) % 2 = 0; exact hp
  have o1 : ¬ EvenSite (x, y + 1) := by unfold EvenSite; show ¬ ((x + (y + 1)) % 2 = 0); omega
  have e2 : EvenSite (x - 1, y + 1) := by unfold EvenSite; show (x - 1 + (y + 1)) % 2 = 0; omega
  have ow : ¬ EvenSite (x - 1, y) := by unfold EvenSite; show ¬ ((x - 1 + y) % 2 = 0); omega
  have ow2 : ¬ EvenSite (x - 1 - 1, y + 1) := by unfold EvenSite; show ¬ ((x - 1 - 1 + (y + 1)) % 2 = 0); omega
  simp only [FreeCutSucc.mem_freeV_iff, closedRect, ChildFrame.vSpectrum, sGrade_eq_w1s,
    if_pos e0, if_neg ow, if_neg o1, if_pos e2, if_neg ow2] at hz ⊢
  simp only [w1t_succY, w1s_succY, w1t_predX, w1s_predX] at hz ⊢
  simp only [tGrade_eq_w1t, sGrade_eq_w1s, frame_periodDenominator_eq] at hlo hs2 hne htp hT2
  generalize w1t frame.child.num frame.child.den (x, y) = t at *
  generalize w1s frame.child.num frame.child.den (x, y) = s at *
  generalize w1T frame.child.num frame.child.den = T at *
  omega

/-- `T` is even when `n` and `d` are odd. -/
theorem periodDenominator_even (frame : ChildFrame) : frame.child.periodDenominator % 2 = 0 := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := frame.child_num_odd
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  obtain ⟨a, ha⟩ : ∃ a : ℤ, frame.child.den = 2 * a + 1 := ⟨frame.child.den / 2, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b : ℤ, frame.child.num = 2 * b + 1 := ⟨frame.child.num / 2, by omega⟩
  have hPQ : frame.child.periodDenominator = 2 * (2 * a ^ 2 + 4 * a + 4 * a * b - 2 * b ^ 2 + 1) := by
    rw [hP, ha, hb]; ring
  rw [hPQ]; exact Int.mul_emod_right 2 _

/-- The V successor exists from an odd site (the lower bound `t ≥ 2d + n − P` is the only input). -/
theorem freeV_succ_of_odd (frame : ChildFrame) {x y : ℤ} (hz : (x, y) ∈ frame.freeV) (hp : (x + y) % 2 = 1)
    (hlo : 2 * frame.child.den + frame.child.num - frame.child.periodDenominator ≤ frame.tGrade (x, y))
    (hT2 : frame.child.periodDenominator % 2 = 0)
    (htp : frame.tGrade (x, y) % 2 = 1) :
    (x, y + 1) ∈ frame.freeV ∨ (x - 1, y + 1) ∈ frame.freeV := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := frame.child_num_odd
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have o0 : ¬ EvenSite (x, y) := by unfold EvenSite; show ¬ ((x + y) % 2 = 0); omega
  have ow : EvenSite (x - 1, y) := by unfold EvenSite; show (x - 1 + y) % 2 = 0; omega
  have e1 : EvenSite (x, y + 1) := by unfold EvenSite; show (x + (y + 1)) % 2 = 0; omega
  have o2 : ¬ EvenSite (x - 1, y + 1) := by unfold EvenSite; show ¬ ((x - 1 + (y + 1)) % 2 = 0); omega
  have e3 : EvenSite (x - 1 - 1, y + 1) := by unfold EvenSite; show (x - 1 - 1 + (y + 1)) % 2 = 0; omega
  simp only [FreeCutSucc.mem_freeV_iff, closedRect, ChildFrame.vSpectrum, sGrade_eq_w1s,
    if_neg o0, if_pos ow, if_pos e1, if_neg o2, if_pos e3] at hz ⊢
  simp only [w1t_succY, w1s_succY, w1t_predX, w1s_predX] at hz ⊢
  simp only [tGrade_eq_w1t, frame_periodDenominator_eq] at hlo hT2 htp
  generalize w1t frame.child.num frame.child.den (x, y) = t at *
  generalize w1s frame.child.num frame.child.den (x, y) = s at *
  generalize w1T frame.child.num frame.child.den = T at *
  omega

/-- **The V successor exists off `vLast`**, split by the parity of `x + y`. -/
theorem freeV_succ_exists (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hne : z ≠ frame.vLast) :
    (z.1, z.2 + 1) ∈ frame.freeV ∨ (z.1 - 1, z.2 + 1) ∈ frame.freeV := by
  obtain ⟨x, y⟩ := z
  have hT2 := periodDenominator_even frame
  rcases Int.emod_two_eq_zero_or_one (x + y) with hp | hp
  · have hev : EvenSite (x, y) := by unfold EvenSite; show (x + y) % 2 = 0; exact hp
    have hlo := (frame.root_bounds hz hev).2.2.1
    have hs2 := (frame.root_bounds hz hev).2.1
    have htp : frame.tGrade (x, y) % 2 = 0 := by
      have h := FanInputs.tGrade_mod_two frame (x, y)
      rw [h]; exact hp
    have hne' : frame.tGrade (x, y) ≠ frame.child.den + frame.child.num - frame.child.periodDenominator :=
      fun h => hne (VLastOfT.vLast_of_tGrade frame hz hev h)
    exact freeV_succ_of_even frame hz hp hT2 hlo hs2 hne' htp
  · have hodd : ¬ EvenSite (x, y) := by unfold EvenSite; show ¬ ((x + y) % 2 = 0); omega
    have hlo := VOddLower.odd_lower_of_mem frame hz hodd
    have htp : frame.tGrade (x, y) % 2 = 1 := by
      have h := FanInputs.tGrade_mod_two frame (x, y)
      rw [h]; exact hp
    exact freeV_succ_of_odd frame hz hp hlo hT2 htp

end FLatticePaper.FreeVCutExist
