import FLatticePaper.Plane.Induction.ArcFrame
import FLatticePaper.Plane.Induction.FanInputs
import FLatticePaper.Plane.Induction.FreeCutSucc

/-! # The H successor exists off `hLast`

For `z ∈ freeH` with `z ≠ hLast`, one of `z + (1,0)` and `z + (1,1)` lies in `freeH`. The grade `t` moves by `+n` or by
`n − d`, and exactly one of these lands in the H spectrum (both-odd `n, d`); the vertex bounds of `freeH_vertex_bounds` keep
the grade `s` inside the polygon; and the exclusion `t ≠ d` (the only `t`-value of `hLast`) is `freeH_eq_hLast_of_tGrade`,
which uses the coprimality of `n` and `d`. -/

namespace FLatticePaper.FreeCutExist

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

theorem tGrade_eq_w1t (frame : ChildFrame) (z : Site) :
    frame.tGrade z = w1t frame.child.num frame.child.den z := rfl

theorem sGrade_eq_w1s (frame : ChildFrame) (z : Site) :
    frame.sGrade z = w1s frame.child.num frame.child.den z := rfl

theorem w1t_succX (n d x y : ℤ) : w1t n d (x + 1, y) = w1t n d (x, y) + n := by
  unfold w1t; ring
theorem w1s_succX (n d x y : ℤ) : w1s n d (x + 1, y) = w1s n d (x, y) + (d + n) := by
  unfold w1s; ring
theorem w1t_predY (n d x y : ℤ) : w1t n d (x, y - 1) = w1t n d (x, y) + d := by
  unfold w1t; ring
theorem w1s_predY (n d x y : ℤ) : w1s n d (x, y - 1) = w1s n d (x, y) + (n - d) := by
  unfold w1s; ring
theorem w1t_succX_predY (n d x y : ℤ) : w1t n d (x + 1, y - 1) = w1t n d (x, y) + n + d := by
  unfold w1t; ring
theorem w1s_succX_predY (n d x y : ℤ) : w1s n d (x + 1, y - 1) = w1s n d (x, y) + 2 * n := by
  unfold w1s; ring
theorem w1t_succXY (n d x y : ℤ) : w1t n d (x + 1, y + 1) = w1t n d (x, y) + n - d := by
  unfold w1t; ring
theorem w1s_succXY (n d x y : ℤ) : w1s n d (x + 1, y + 1) = w1s n d (x, y) + 2 * d := by
  unfold w1s; ring

/-- A free H site with `t = d` is `hLast`: `n z₁ = d (z₂ + 1)` with `1 ≤ z₁ ≤ d` and `gcd(n, d) = 1` forces `z₁ = d`. -/
theorem freeH_eq_hLast_of_tGrade (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH)
    (ht : frame.tGrade z = frame.child.den) : z = frame.hLast := by
  obtain ⟨hn, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := FanInputs.num_odd frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have hcop : IsCoprime frame.child.den frame.child.num := frame.child_reduced.symm
  obtain ⟨z1, z2⟩ := z
  have hpar := FanInputs.tGrade_mod_two frame (z1, z2)
  rw [ht] at hpar
  have hodd : ¬ EvenSite (z1, z2) := by
    unfold EvenSite
    dsimp only at hpar ⊢
    omega
  rw [FreeCutSucc.mem_freeH_iff] at hz
  obtain ⟨hz1, -, hz3⟩ := hz
  unfold closedRect at hz1
  rw [if_neg hodd] at hz1
  simp only [tGrade_eq_w1t, ChildFrame.hSpectrum, w1t, w1s, w1T] at hz1 hz3 ht
  have ht1 : frame.child.num ≤ frame.child.num * z1 - frame.child.den * z2 := by
    rw [ht]; omega
  have ht2 : frame.child.num * z1 - frame.child.den * z2 ≤ frame.child.den := by
    rw [ht]
  obtain ⟨hz2lo, hz2hi, hz1lo, hz1hi, -, -⟩ := FLatticePaper.ArcBounds.arc_odd_bounds
    frame.child.num frame.child.den z1 z2 (by omega) (by omega) (by omega) ht1 ht2 (by omega) (by nlinarith)
  have hdvd : frame.child.den ∣ frame.child.num * z1 := ⟨z2 + 1, by linarith⟩
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left hdvd
  have hk0 : 0 < k := by
    by_contra h
    have h' : k ≤ 0 := by omega
    nlinarith
  have hk1 : k < 2 := by
    by_contra h
    have h' : 2 ≤ k := by omega
    nlinarith
  have hk' : k = 1 := by omega
  subst hk'
  have hz1eq : z1 = frame.child.den := by linarith
  subst hz1eq
  have hz2eq : z2 = frame.child.num - 1 := by
    have h : frame.child.den * z2 = frame.child.den * (frame.child.num - 1) := by linarith
    exact mul_left_cancel₀ (by omega) h
  unfold ChildFrame.hLast
  rw [hz2eq]


/-- **The H successor exists from an even site.** The candidate `z + (1,0)` is odd and `z + (1,1)` is even; the grades of the
candidates are linear in the grades of `(x, y)`, and the parity of `t` is that of `x + y` (both-odd `n, d`). -/
theorem freeH_succ_of_even (frame : ChildFrame) {x y : ℤ} (hz : (x, y) ∈ frame.freeH) (hp : (x + y) % 2 = 0) :
    (x + 1, y) ∈ frame.freeH ∨ (x + 1, y + 1) ∈ frame.freeH := by
  obtain ⟨hn, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := FanInputs.num_odd frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have hsb := (ArcFrame.freeH_vertex_bounds frame hnodd hdodd hz).1
    (by unfold EvenSite; show (x + y) % 2 = 0; exact hp)
  have hpar : w1t frame.child.num frame.child.den (x, y) % 2 = (x + y) % 2 := by
    have h := FanInputs.tGrade_mod_two frame (x, y)
    simpa [tGrade_eq_w1t] using h
  have hTd : 2 * frame.child.den ≤ w1T frame.child.num frame.child.den := by
    unfold w1T; nlinarith
  have e0 : EvenSite (x, y) := by unfold EvenSite; show (x + y) % 2 = 0; exact hp
  have o1 : ¬ EvenSite (x, y - 1) := by unfold EvenSite; show ¬ ((x + (y - 1)) % 2 = 0); omega
  have o2 : ¬ EvenSite (x + 1, y) := by unfold EvenSite; show ¬ ((x + 1 + y) % 2 = 0); omega
  have e2 : EvenSite (x + 1, y + 1) := by unfold EvenSite; show (x + 1 + (y + 1)) % 2 = 0; omega
  have e3 : EvenSite (x + 1, y - 1) := by unfold EvenSite; show (x + 1 + (y - 1)) % 2 = 0; omega
  simp only [sGrade_eq_w1s, frame_periodDenominator_eq] at hsb
  simp only [FreeCutSucc.mem_freeH_iff, closedRect, if_pos e0, if_neg o1, if_neg o2, if_pos e2, if_pos e3,
    add_sub_cancel_right, ChildFrame.hSpectrum, tGrade_eq_w1t] at hz ⊢
  simp only [w1t_succX_predY, w1s_succX_predY, w1t_succXY, w1s_succXY] at hz ⊢
  simp only [w1t_predY, w1s_predY, w1t_succX, w1s_succX] at hz ⊢
  generalize w1t frame.child.num frame.child.den (x, y) = t at *
  generalize w1s frame.child.num frame.child.den (x, y) = s at *
  generalize w1T frame.child.num frame.child.den = T at *
  omega

/-- **The H successor exists from an odd site** (with `t ≠ d`, i.e. `z ≠ hLast`). The candidate `z + (1,0)` is even and
`z + (1,1)` is odd; the bounds `d + n ≤ s ≤ T − (d − n)` of the odd free H sites keep the candidate in the polygon. -/
theorem freeH_succ_of_odd (frame : ChildFrame) {x y : ℤ} (hz : (x, y) ∈ frame.freeH) (hp : (x + y) % 2 = 1)
    (hne : frame.tGrade (x, y) ≠ frame.child.den) :
    (x + 1, y) ∈ frame.freeH ∨ (x + 1, y + 1) ∈ frame.freeH := by
  obtain ⟨hn, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := FanInputs.num_odd frame
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have hsb := (ArcFrame.freeH_vertex_bounds frame hnodd hdodd hz).2
    (by unfold EvenSite; show ¬ ((x + y) % 2 = 0); omega)
  have hpar : w1t frame.child.num frame.child.den (x, y) % 2 = (x + y) % 2 := by
    have h := FanInputs.tGrade_mod_two frame (x, y)
    simpa [tGrade_eq_w1t] using h
  have htne : w1t frame.child.num frame.child.den (x, y) ≠ frame.child.den := by
    simpa [tGrade_eq_w1t] using hne
  have e0 : ¬ EvenSite (x, y) := by unfold EvenSite; show ¬ ((x + y) % 2 = 0); omega
  have o1 : EvenSite (x, y - 1) := by unfold EvenSite; show (x + (y - 1)) % 2 = 0; omega
  have e2 : EvenSite (x + 1, y) := by unfold EvenSite; show (x + 1 + y) % 2 = 0; omega
  have o3 : ¬ EvenSite (x + 1, y - 1) := by unfold EvenSite; show ¬ ((x + 1 + (y - 1)) % 2 = 0); omega
  have o4 : ¬ EvenSite (x + 1, y + 1) := by unfold EvenSite; show ¬ ((x + 1 + (y + 1)) % 2 = 0); omega
  simp only [sGrade_eq_w1s, frame_periodDenominator_eq] at hsb
  simp only [FreeCutSucc.mem_freeH_iff, closedRect, if_neg e0, if_pos o1, if_pos e2, if_neg o3, if_neg o4,
    add_sub_cancel_right, ChildFrame.hSpectrum, tGrade_eq_w1t] at hz ⊢
  simp only [w1t_succX_predY, w1s_succX_predY, w1t_succXY, w1s_succXY] at hz ⊢
  simp only [w1t_predY, w1s_predY, w1t_succX, w1s_succX] at hz ⊢
  generalize w1t frame.child.num frame.child.den (x, y) = t at *
  generalize w1s frame.child.num frame.child.den (x, y) = s at *
  generalize w1T frame.child.num frame.child.den = T at *
  omega

/-- **The H successor exists off `hLast`**, split by the parity of `x + y`. -/
theorem freeH_succ_exists (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hne : z ≠ frame.hLast) :
    (z.1 + 1, z.2) ∈ frame.freeH ∨ (z.1 + 1, z.2 + 1) ∈ frame.freeH := by
  obtain ⟨x, y⟩ := z
  rcases Int.emod_two_eq_zero_or_one (x + y) with hp | hp
  · exact freeH_succ_of_even frame hz hp
  · exact freeH_succ_of_odd frame hz hp (fun h => hne (freeH_eq_hLast_of_tGrade frame hz h))

end FLatticePaper.FreeCutExist
