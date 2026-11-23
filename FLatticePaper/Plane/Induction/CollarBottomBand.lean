import FLatticePaper.Plane.Induction.VPathFloor

/-! Task 72 (hcollar, band (a), the bottom corners): the H points of the closed polygon have a floor law and a lower `s`-bound.

* Even H points `v` (`t(v) ∈ [2, L − 2]`): `v.2 = ⌊2 n l / L⌋` with `l = (v.1 + v.2)/2`, so `l ≥ 1`, `v.2 ≤ l − 1` and
  `s(v) = 2 L l − 2 n v.2 ≥ 2 d l + 2 n`.
* Odd H points `v` (`t(v) ∈ [n, d]`): with `k = v.1 + v.2`, either `v = (1, 0)` (so `s(v) = L`) or `s(v) ≥ 3 L`.

These are the inputs of the bottom band `s > 2L − 2` (even, except the black corner `(1,1)`) and `s > L + 2n` (odd). -/

namespace FLatticePaper.CollarBottomBand

open Farey FLatticePaper FLatticePaper.Induction

/-- The even H points of the closed polygon: `l ≥ 1`, `v.2 ≤ l − 1` and the `s`-lower bound. -/
theorem even_H_bounds (frame : ChildFrame) {v : Site} (hv : EvenSite v) (hE : v ∈ frame.closedPolygon)
    (hsp : frame.hSpectrum (frame.tGrade v)) :
    ∃ l : ℤ, v.1 + v.2 = 2 * l ∧ 1 ≤ l ∧ v.2 ≤ l - 1 ∧
      2 * frame.child.den * l + 2 * frame.child.num ≤ frame.sGrade v := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  obtain ⟨l, hl⟩ : ∃ l : ℤ, v.1 + v.2 = 2 * l := ⟨(v.1 + v.2) / 2, by unfold EvenSite at hv; omega⟩
  have hdiv : (v.1 + v.2) / 2 = l := by omega
  have hfl := even_spectrum_floor frame hv hsp
  rw [hdiv] at hfl
  have hL : 0 < frame.child.den + frame.child.num := by omega
  -- the spectrum and the polygon
  unfold ChildFrame.hSpectrum at hsp
  have ht : 2 ≤ frame.tGrade v ∧ frame.tGrade v ≤ frame.child.den + frame.child.num - 2 := by
    rcases hsp with ⟨-, h1, h2⟩ | ⟨h3, -, -⟩
    · exact ⟨h1, h2⟩
    · unfold EvenSite at hv
      obtain ⟨c, hc⟩ := frame.tGrade_parity v
      omega
  have hs0 : 0 ≤ frame.sGrade v := by
    rw [frame.mem_closedPolygon_iff] at hE
    simp only [EvenSite] at hE
    rcases hE with ⟨-, -, -, h, -⟩ | ⟨h, -⟩
    · exact h
    · exact absurd hv h
  unfold ChildFrame.tGrade at ht
  unfold ChildFrame.sGrade at hs0 ⊢
  -- l ≥ 1
  have hl1 : 1 ≤ l := by
    by_contra hc
    have hl0 : v.1 + v.2 ≤ 0 := by omega
    generalize frame.child.num = n at *
    generalize frame.child.den = d at *
    generalize v.1 = x at *
    generalize v.2 = y at *
    have hx : 0 ≤ x := by nlinarith
    have hx0 : x = 0 := by nlinarith
    subst hx0
    nlinarith
  -- v.2 ≤ l − 1 from the floor identity
  have hlt : v.2 < l := by
    rw [hfl]
    rw [Int.ediv_lt_iff_lt_mul hL]
    nlinarith
  refine ⟨l, hl, hl1, by omega, ?_⟩
  have hv1 : v.1 = 2 * l - v.2 := by omega
  rw [hv1] at hs0 ⊢
  nlinarith

/-- The odd H points of the closed polygon: either `v = (1, 0)` (with `s = L`) or `s(v) ≥ 3 L`. -/
theorem odd_H_bounds (frame : ChildFrame) {v : Site} (hv : ¬ EvenSite v) (hE : v ∈ frame.closedPolygon)
    (hsp : frame.hSpectrum (frame.tGrade v)) :
    v = (1, 0) ∨ 3 * (frame.child.den + frame.child.num) ≤ frame.sGrade v := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hL : 0 < frame.child.den + frame.child.num := by omega
  unfold ChildFrame.hSpectrum at hsp
  have ht : frame.child.num ≤ frame.tGrade v ∧ frame.tGrade v ≤ frame.child.den := by
    rcases hsp with ⟨h1, -, -⟩ | ⟨-, h2, h3⟩
    · exfalso
      obtain ⟨c, hc⟩ := frame.tGrade_parity v
      unfold EvenSite at hv
      omega
    · exact ⟨h2, h3⟩
  have hsE : 2 - frame.child.den + frame.child.num ≤ frame.sGrade v := by
    rw [frame.mem_closedPolygon_iff] at hE
    simp only [EvenSite] at hE
    rcases hE with ⟨h, -⟩ | ⟨-, -, -, h, -⟩
    · exact absurd h hv
    · exact h
  obtain ⟨x, y⟩ := v
  unfold ChildFrame.tGrade at ht
  unfold ChildFrame.sGrade at hsE ⊢
  unfold EvenSite at hv
  dsimp only at hv ht hsE ⊢
  generalize frame.child.num = n at *
  generalize frame.child.den = d at *
  obtain ⟨k, hk⟩ : ∃ k : ℤ, x + y = k := ⟨_, rfl⟩
  have hx : x = k - y := by omega
  subst hx
  have hkodd : k % 2 = 1 := by omega
  have key : (d + n) * ((d + n) * (k - y) + (d - n) * y) =
      k * ((d + n) ^ 2 - 2 * n ^ 2) + 2 * n * (n * (k - y) - d * y) := by ring
  have hpos : 0 < (d + n) ^ 2 - 2 * n ^ 2 := by nlinarith
  rcases (show k ≤ -1 ∨ k = 1 ∨ k = 3 ∨ 5 ≤ k by omega) with hk1 | hk1 | hk1 | hk1
  · exfalso
    have h1 : k * ((d + n) ^ 2 - 2 * n ^ 2) ≤ -((d + n) ^ 2 - 2 * n ^ 2) := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ -1 - k by omega) hpos.le]
    have h2 : 2 * n * (n * (k - y) - d * y) ≤ 2 * n * d := by
      nlinarith [mul_le_mul_of_nonneg_left ht.2 (show (0 : ℤ) ≤ 2 * n by omega)]
    have h3 := mul_le_mul_of_nonneg_left hsE hL.le
    nlinarith
  · left
    have hLy : (d + n) * y ≤ 0 := by nlinarith
    have hLy' : -(d + n) < (d + n) * y := by nlinarith
    have hy0 : y ≤ 0 := by
      by_contra h
      have h' : 1 ≤ y := by omega
      nlinarith
    have hy1 : 0 ≤ y := by
      by_contra h
      have h' : y ≤ -1 := by omega
      nlinarith
    have hy : y = 0 := by omega
    have hx : k - y = 1 := by omega
    rw [hx, hy]
  · right
    have hLy : (d + n) * y ≤ 2 * n := by nlinarith
    have hy0 : y ≤ 0 := by
      by_contra h
      have h' : 1 ≤ y := by omega
      nlinarith
    nlinarith
  · right
    have hLy : (d + n) * y ≤ n * (k - 1) := by nlinarith
    have h1 : (d + n) * (2 * n * y) ≤ (d + n) * ((d + n) * (k - 3)) := by
      nlinarith [mul_le_mul_of_nonneg_left hLy hn0.le]
    have h2 : 2 * n * y ≤ (d + n) * (k - 3) := le_of_mul_le_mul_left h1 hL
    nlinarith

end FLatticePaper.CollarBottomBand
