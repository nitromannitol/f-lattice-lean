import FLatticePaper.Plane.Induction.FreeHPrice

/-! The even-root bound of the east tip step (sign `+1`).

For a child frame with `n`, `d` both odd (`child_odd`), the sheet grade `s = (d+n) x + (d−n) y` on the box `1 ≤ x ≤ d`, `0 ≤ y ≤ n−1`
has maximum `T − d + n` (`s_box`), attained only at the corner `(d, n−1)`, whose coordinate sum `d + n − 1` is odd. Since `d ± n` and
`T − d + n` are even, an even point of the box has `s ≤ T − d + n − 2`. -/

namespace FLatticePaper.TipEast

open Farey FLatticePaper FLatticePaper.Induction

theorem even_s_le (frame : ChildFrame) {x y : ℤ} (hx1 : 1 ≤ x) (hxd : x ≤ frame.child.den)
    (hy0 : 0 ≤ y) (hyn : y ≤ frame.child.num - 1) (hev : (x + y) % 2 = 0) :
    (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y ≤
      frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num
        - frame.child.den + frame.child.num - 2 := by
  obtain ⟨hco1, hco2⟩ := frame.child_odd
  obtain ⟨hn0, hnd, -, -, -⟩ := frame.child_facts
  have hnd2 : frame.child.num + 2 ≤ frame.child.den := by omega
  have hsb := FLatticePaper.PriceInputs.s_box frame.child.num frame.child.den x y hn0 hnd2 hx1 hxd hy0 hyn
  obtain ⟨p, hp⟩ : ∃ p, frame.child.den + frame.child.num = 2 * p := ⟨(frame.child.den + frame.child.num) / 2, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, frame.child.den - frame.child.num = 2 * q := ⟨(frame.child.den - frame.child.num) / 2, by omega⟩
  have hsEven : (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y =
      2 * (p * x + q * y) := by
    rw [hp, hq]
    ring
  have hKeven : frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num
      - frame.child.den + frame.child.num = 2 * (q * (2 * p - 1) + frame.child.den * frame.child.num) := by
    linear_combination (frame.child.den + frame.child.num - 1) * hq + 2 * q * hp
  have hne : (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y ≠
      frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num
        - frame.child.den + frame.child.num := by
    intro heq
    have hid : (frame.child.den + frame.child.num) * (frame.child.den - x) +
        (frame.child.den - frame.child.num) * (frame.child.num - 1 - y) = 0 := by
      linear_combination (-1 : ℤ) * heq
    have t1 : 0 ≤ (frame.child.den + frame.child.num) * (frame.child.den - x) :=
      mul_nonneg (by omega) (by omega)
    have t2 : 0 ≤ (frame.child.den - frame.child.num) * (frame.child.num - 1 - y) :=
      mul_nonneg (by omega) (by omega)
    have e1 : (frame.child.den + frame.child.num) * (frame.child.den - x) = 0 := by linarith
    have e2 : (frame.child.den - frame.child.num) * (frame.child.num - 1 - y) = 0 := by linarith
    have hx : x = frame.child.den := by
      rcases mul_eq_zero.mp e1 with h | h <;> omega
    have hy : y = frame.child.num - 1 := by
      rcases mul_eq_zero.mp e2 with h | h <;> omega
    omega
  generalize (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y = s at hsEven hne hsb ⊢
  generalize frame.child.den * frame.child.den + 2 * frame.child.den * frame.child.num - frame.child.num * frame.child.num
      - frame.child.den + frame.child.num = K at hKeven hne hsb ⊢
  generalize p * x + q * y = m at hsEven
  generalize q * (2 * p - 1) + frame.child.den * frame.child.num = k at hKeven
  omega

end FLatticePaper.TipEast
