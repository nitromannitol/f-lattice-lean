import FLatticePaper.Plane.Induction.NonfreeBridge
import FLatticePaper.Plane.Induction.ShortPassages

/-! Task 72 (upstream input of FIXED_FREE §3/§4): the staircase box of the free H trace.

`ChildFrame.freeH` is the bottom boundary of `closedPolygon` with `hSpectrum t`. Every free H site `z = (x, y)` satisfies
`1 ≤ x ≤ d` and `0 ≤ y ≤ n − 1`. The proof uses only the grade bounds of the closed polygon and the H spectrum, with `x, y` integers:
the lower bound `y ≥ 0` (resp. `y ≤ n − 1`) is ruled out by an integer bound `x ≥ 1` (resp. `x ≥ d + 1`) that contradicts the polygon,
and the `x` bounds then follow from `y`.

What this module does NOT give: the root windows of the route theorems (for instance `c + 2 ≤ t(z)` in `H_EN_middle_nonfree`) are not
consequences of `z ∈ freeH`. A free even H site `(2, 0)` of the trace `(n, d) = (1, 3)` has `t = 2 < c + 2 = 4`, and its E-step
`(3, 0)` is itself a free H site. See `scripts/free_trace_route_check.py`. -/

namespace FLatticePaper.Induction

namespace FreeTraceBox

open ShortPassages

/-- The box for even sites: `1 ≤ t ≤ L − 2` and `0 ≤ s ≤ T + 2n` with `t = n x − d y`, `s = L x + (d − n) y`. -/
theorem box_even (N D x y : ℤ) (hN : 1 ≤ N) (hND : N + 2 ≤ D)
    (h1 : 1 ≤ N * x - D * y) (h2 : N * x - D * y ≤ D + N - 2)
    (h3 : 0 ≤ (D + N) * x + (D - N) * y)
    (h4 : (D + N) * x + (D - N) * y ≤ (D ^ 2 + 2 * D * N - N ^ 2) + 2 * N) :
    1 ≤ x ∧ x ≤ D ∧ 0 ≤ y ∧ y ≤ N - 1 := by
  have hy0 : 0 ≤ y := by
    by_contra h
    have hy1 : y ≤ -1 := by omega
    have hx : 1 ≤ x := by
      by_contra hx
      have hx0 : x ≤ 0 := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ D + N by omega) (show (0 : ℤ) ≤ -x by omega),
        mul_nonneg (show (0 : ℤ) ≤ D - N by omega) (show (0 : ℤ) ≤ -1 - y by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ N by omega) (show (0 : ℤ) ≤ x - 1 by omega),
      mul_nonneg (show (0 : ℤ) ≤ D by omega) (show (0 : ℤ) ≤ -1 - y by omega)]
  have hyN : y ≤ N - 1 := by
    by_contra h
    have hy : N ≤ y := by omega
    have hxD : D + 1 ≤ x := by
      have h5 : N * D < N * x := by
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ D by omega) (show (0 : ℤ) ≤ y - N by omega)]
      have h6 : D < x := lt_of_mul_lt_mul_left h5 (by omega)
      omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ D + N by omega) (show (0 : ℤ) ≤ x - (D + 1) by omega),
      mul_nonneg (show (0 : ℤ) ≤ D - N by omega) (show (0 : ℤ) ≤ y - N by omega)]
  have hxD : x ≤ D := by
    by_contra h
    have hx : D + 1 ≤ x := by omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ N by omega) (show (0 : ℤ) ≤ x - (D + 1) by omega),
      mul_nonneg (show (0 : ℤ) ≤ D by omega) (show (0 : ℤ) ≤ N - 1 - y by omega)]
  have hx1 : 1 ≤ x := by
    by_contra h
    have hx0 : x ≤ 0 := by omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ N by omega) (show (0 : ℤ) ≤ -x by omega),
      mul_nonneg (show (0 : ℤ) ≤ D by omega) (show (0 : ℤ) ≤ y by omega)]
  exact ⟨hx1, hxD, hy0, hyN⟩

/-- The box for odd sites: `n ≤ t ≤ d` and `2 − (d − n) ≤ s ≤ T + L − 2`. -/
theorem box_odd (N D x y : ℤ) (hN : 1 ≤ N) (hND : N + 2 ≤ D)
    (h1 : N ≤ N * x - D * y) (h2 : N * x - D * y ≤ D)
    (h3 : 2 - (D - N) ≤ (D + N) * x + (D - N) * y)
    (h4 : (D + N) * x + (D - N) * y ≤ (D ^ 2 + 2 * D * N - N ^ 2) + (D + N) - 2) :
    1 ≤ x ∧ x ≤ D ∧ 0 ≤ y ∧ y ≤ N - 1 := by
  have hy0 : 0 ≤ y := by
    by_contra h
    have hy1 : y ≤ -1 := by omega
    have hx : 1 ≤ x := by
      by_contra hx
      have hx0 : x ≤ 0 := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ D + N by omega) (show (0 : ℤ) ≤ -x by omega),
        mul_nonneg (show (0 : ℤ) ≤ D - N by omega) (show (0 : ℤ) ≤ -1 - y by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ N by omega) (show (0 : ℤ) ≤ x - 1 by omega),
      mul_nonneg (show (0 : ℤ) ≤ D by omega) (show (0 : ℤ) ≤ -1 - y by omega)]
  have hyN : y ≤ N - 1 := by
    by_contra h
    have hy : N ≤ y := by omega
    have hxD : D + 1 ≤ x := by
      have h5 : N * D < N * x := by
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ D by omega) (show (0 : ℤ) ≤ y - N by omega)]
      have h6 : D < x := lt_of_mul_lt_mul_left h5 (by omega)
      omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ D + N by omega) (show (0 : ℤ) ≤ x - (D + 1) by omega),
      mul_nonneg (show (0 : ℤ) ≤ D - N by omega) (show (0 : ℤ) ≤ y - N by omega)]
  have hxD : x ≤ D := by
    by_contra h
    have hx : D + 1 ≤ x := by omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ N by omega) (show (0 : ℤ) ≤ x - (D + 1) by omega),
      mul_nonneg (show (0 : ℤ) ≤ D by omega) (show (0 : ℤ) ≤ N - 1 - y by omega)]
  have hx1 : 1 ≤ x := by
    by_contra h
    have hx0 : x ≤ 0 := by omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ N by omega) (show (0 : ℤ) ≤ -x by omega),
      mul_nonneg (show (0 : ℤ) ≤ D by omega) (show (0 : ℤ) ≤ y by omega)]
  exact ⟨hx1, hxD, hy0, hyN⟩

/-- **The staircase box of the free H trace.** Every free H site `z` lies in `1 ≤ z.1 ≤ d`, `0 ≤ z.2 ≤ n − 1`. -/
theorem freeH_box (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) :
    1 ≤ z.1 ∧ z.1 ≤ frame.child.den ∧ 0 ≤ z.2 ∧ z.2 ≤ frame.child.num - 1 := by
  obtain ⟨x, y⟩ := z
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz
  obtain ⟨hE, -, hS⟩ := hz
  obtain ⟨hTd, hN0, hND, -⟩ := period_facts frame
  have hN : 1 ≤ frame.child.num := by omega
  rw [FLatticePaper.Induction.mem_closedPolygon_iff] at hE
  have hpar : frame.tGrade (x, y) % 2 = (x + y) % 2 := FLatticePaper.Induction.tGrade_parity frame (x, y)
  have htdef : frame.tGrade (x, y) = frame.child.num * x - frame.child.den * y := rfl
  have hsdef : frame.sGrade (x, y) =
      (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y := rfl
  set t := frame.tGrade (x, y) with ht
  set s := frame.sGrade (x, y) with hs
  unfold ChildFrame.hSpectrum at hS
  by_cases he : (x + y) % 2 = 0
  · have hEv : EvenSite (x, y) := he
    rw [if_pos hEv] at hE
    obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
    have ht1 : 1 ≤ t := by
      rcases hS with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> omega
    have hbox := box_even frame.child.num frame.child.den x y hN hND
      (by linarith) (by linarith) (by linarith) (by linarith)
    exact ⟨hbox.1, hbox.2.1, hbox.2.2.1, hbox.2.2.2⟩
  · have hEv : ¬ EvenSite (x, y) := he
    rw [if_neg hEv] at hE
    obtain ⟨hE1, hE2, hE3, hE4⟩ := hE
    have ht2 : frame.child.num ≤ t ∧ t ≤ frame.child.den := by
      rcases hS with ⟨h1, -, -⟩ | ⟨-, h2, h3⟩
      · omega
      · exact ⟨h2, h3⟩
    have hbox := box_odd frame.child.num frame.child.den x y hN hND
      (by linarith [ht2.1]) (by linarith [ht2.2]) (by linarith) (by linarith)
    exact ⟨hbox.1, hbox.2.1, hbox.2.2.1, hbox.2.2.2⟩

end FreeTraceBox

end FLatticePaper.Induction
