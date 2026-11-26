import FLatticePaper.Plane.Induction.FreeCutExist
import FLatticePaper.Plane.Induction.FreeVCutExist
import FLatticePaper.Plane.Induction.VOddLower
import FLatticePaper.Plane.Induction.HX2Diag
import FLatticePaper.Plane.Induction.ArcFrame
import FLatticePaper.Plane.Induction.FreeCutSucc

/-! # The predecessors of the free cuts

For `z ∈ freeH` with `z ≠ hFirst`, one of `z - (1,0)` and `z - (1,1)` lies in `freeH`. The H candidates move `t` by `-n` or by
`-n + d`. For `z ∈ freeV` with `z ≠ vFirst`, one of `z - (0,1)` and `z + (1,-1)` lies in `freeV`. -/

namespace FLatticePaper.FreeCutPred

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1

theorem tGrade_eq_w1t (frame : ChildFrame) (z : Site) :
    frame.tGrade z = w1t frame.child.num frame.child.den z := rfl

theorem sGrade_eq_w1s (frame : ChildFrame) (z : Site) :
    frame.sGrade z = w1s frame.child.num frame.child.den z := rfl

theorem w1t_predX (n d x y : ℤ) : w1t n d (x - 1, y) = w1t n d (x, y) - n := by unfold w1t; ring
theorem w1s_predX (n d x y : ℤ) : w1s n d (x - 1, y) = w1s n d (x, y) - (d + n) := by unfold w1s; ring
theorem w1t_predY (n d x y : ℤ) : w1t n d (x, y - 1) = w1t n d (x, y) + d := by unfold w1t; ring
theorem w1s_predY (n d x y : ℤ) : w1s n d (x, y - 1) = w1s n d (x, y) + (n - d) := by unfold w1s; ring
theorem w1t_succX (n d x y : ℤ) : w1t n d (x + 1, y) = w1t n d (x, y) + n := by unfold w1t; ring
theorem w1s_succX (n d x y : ℤ) : w1s n d (x + 1, y) = w1s n d (x, y) + (d + n) := by unfold w1s; ring
theorem w1t_succY (n d x y : ℤ) : w1t n d (x, y + 1) = w1t n d (x, y) - d := by unfold w1t; ring
theorem w1s_succY (n d x y : ℤ) : w1s n d (x, y + 1) = w1s n d (x, y) + (d - n) := by unfold w1s; ring

/-- A free H site with `t = n` is `hFirst`: `n (z₁ - 1) = d z₂` with `1 ≤ z₁ ≤ d` and `gcd(n, d) = 1` forces `z₁ = 1`, `z₂ = 0`. -/
theorem freeH_eq_hFirst_of_tGrade (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH)
    (ht : frame.tGrade z = frame.child.num) : z = FLatticePaper.Induction.hFirst := by
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
  have ht1 : frame.child.num ≤ frame.child.num * z1 - frame.child.den * z2 := by omega
  have ht2 : frame.child.num * z1 - frame.child.den * z2 ≤ frame.child.den := by omega
  obtain ⟨hz2lo, hz2hi, hz1lo, hz1hi, -, -⟩ := FLatticePaper.ArcBounds.arc_odd_bounds
    frame.child.num frame.child.den z1 z2 (by omega) (by omega) (by omega) ht1 ht2 (by omega) (by nlinarith)
  have hdvd : frame.child.den ∣ frame.child.num * (z1 - 1) := ⟨z2, by linear_combination ht⟩
  obtain ⟨k, hk⟩ := hcop.dvd_of_dvd_mul_left hdvd
  have hk0 : k = 0 := by
    rcases lt_trichotomy k 0 with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  subst hk0
  have hz1eq : z1 = 1 := by omega
  subst hz1eq
  have hz2eq : z2 = 0 := by
    have h : frame.child.den * z2 = 0 := by linarith
    exact (mul_eq_zero.mp h).resolve_left (by omega)
  unfold FLatticePaper.Induction.hFirst
  rw [hz2eq]

/-- The H predecessor exists from an even site. -/
theorem freeH_pred_of_even (frame : ChildFrame) {x y : ℤ} (hz : (x, y) ∈ frame.freeH) (hp : (x + y) % 2 = 0) :
    (x - 1, y) ∈ frame.freeH ∨ (x - 1, y - 1) ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := frame.child_num_odd
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have hsb := (ArcFrame.freeH_vertex_bounds frame hnodd hdodd hz).1
    (by unfold EvenSite; show (x + y) % 2 = 0; exact hp)
  have hpar : w1t frame.child.num frame.child.den (x, y) % 2 = (x + y) % 2 := by
    have h := FanInputs.tGrade_mod_two frame (x, y)
    simpa [tGrade_eq_w1t] using h
  have e0 : EvenSite (x, y) := by unfold EvenSite; show (x + y) % 2 = 0; exact hp
  have os : ¬ EvenSite (x, y - 1) := by unfold EvenSite; show ¬ ((x + (y - 1)) % 2 = 0); omega
  have o1 : ¬ EvenSite (x - 1, y) := by unfold EvenSite; show ¬ ((x - 1 + y) % 2 = 0); omega
  have e1 : EvenSite (x - 1, y - 1) := by unfold EvenSite; show (x - 1 + (y - 1)) % 2 = 0; omega
  have o2 : ¬ EvenSite (x - 1, y - 1 - 1) := by
    unfold EvenSite; show ¬ ((x - 1 + (y - 1 - 1)) % 2 = 0); omega
  simp only [sGrade_eq_w1s, frame_periodDenominator_eq] at hsb
  simp only [FreeCutSucc.mem_freeH_iff, closedRect, ChildFrame.hSpectrum, tGrade_eq_w1t,
    if_pos e0, if_neg os, if_neg o1, if_pos e1, if_neg o2] at hz ⊢
  simp only [w1t_predX, w1s_predX, w1t_predY, w1s_predY] at hz ⊢
  generalize w1t frame.child.num frame.child.den (x, y) = t at *
  generalize w1s frame.child.num frame.child.den (x, y) = s at *
  generalize w1T frame.child.num frame.child.den = T at *
  omega

/-- The H predecessor exists from an odd site (with `t ≠ n`, i.e. `z ≠ hFirst`). -/
theorem freeH_pred_of_odd (frame : ChildFrame) {x y : ℤ} (hz : (x, y) ∈ frame.freeH) (hp : (x + y) % 2 = 1)
    (hne : frame.tGrade (x, y) ≠ frame.child.num) :
    (x - 1, y) ∈ frame.freeH ∨ (x - 1, y - 1) ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := frame.child_num_odd
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have hsb := (ArcFrame.freeH_vertex_bounds frame hnodd hdodd hz).2
    (by unfold EvenSite; show ¬ ((x + y) % 2 = 0); omega)
  have hpar : w1t frame.child.num frame.child.den (x, y) % 2 = (x + y) % 2 := by
    have h := FanInputs.tGrade_mod_two frame (x, y)
    simpa [tGrade_eq_w1t] using h
  have htne : w1t frame.child.num frame.child.den (x, y) ≠ frame.child.num := by
    simpa [tGrade_eq_w1t] using hne
  have o0 : ¬ EvenSite (x, y) := by unfold EvenSite; show ¬ ((x + y) % 2 = 0); omega
  have es : EvenSite (x, y - 1) := by unfold EvenSite; show (x + (y - 1)) % 2 = 0; omega
  have ep1 : EvenSite (x - 1, y) := by unfold EvenSite; show (x - 1 + y) % 2 = 0; omega
  have op1s : ¬ EvenSite (x - 1, y - 1) := by unfold EvenSite; show ¬ ((x - 1 + (y - 1)) % 2 = 0); omega
  have ep2s : EvenSite (x - 1, y - 1 - 1) := by
    unfold EvenSite; show (x - 1 + (y - 1 - 1)) % 2 = 0; omega
  simp only [sGrade_eq_w1s, frame_periodDenominator_eq] at hsb
  simp only [FreeCutSucc.mem_freeH_iff, closedRect, ChildFrame.hSpectrum, tGrade_eq_w1t,
    if_neg o0, if_pos es, if_pos ep1, if_neg op1s, if_pos ep2s] at hz ⊢
  simp only [w1t_predX, w1s_predX, w1t_predY, w1s_predY] at hz ⊢
  generalize w1t frame.child.num frame.child.den (x, y) = t at *
  generalize w1s frame.child.num frame.child.den (x, y) = s at *
  generalize w1T frame.child.num frame.child.den = T at *
  omega

/-- **The H predecessor exists off `hFirst`**, split by the parity of `x + y`. -/
theorem freeH_pred_exists (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH)
    (hne : z ≠ FLatticePaper.Induction.hFirst) :
    (z.1 - 1, z.2) ∈ frame.freeH ∨ (z.1 - 1, z.2 - 1) ∈ frame.freeH := by
  obtain ⟨x, y⟩ := z
  rcases Int.emod_two_eq_zero_or_one (x + y) with hp | hp
  · exact freeH_pred_of_even frame hz hp
  · exact freeH_pred_of_odd frame hz hp (fun h => hne (freeH_eq_hFirst_of_tGrade frame hz h))

theorem w1t_refl (n d x y : ℤ) :
    w1t n d (n - d + 1 - x, n + d - 1 - y) = (d + n - w1T n d) - w1t n d (x, y) := by
  unfold w1t w1T; ring
theorem w1s_refl (n d x y : ℤ) :
    w1s n d (n - d + 1 - x, n + d - 1 - y) = 2 * n - w1s n d (x, y) := by
  unfold w1s; ring
theorem w1t_refl_west (n d x y : ℤ) :
    w1t n d (n - d + 1 - x - 1, n + d - 1 - y) = (d + n - w1T n d) - (w1t n d (x, y) + n) := by
  unfold w1t w1T; ring
theorem w1s_refl_west (n d x y : ℤ) :
    w1s n d (n - d + 1 - x - 1, n + d - 1 - y) = 2 * n - (w1s n d (x, y) + (d + n)) := by
  unfold w1s; ring

/-- **The reflection `z ↦ vLast - z` preserves the free V cut, from an even site.** The image has grades `(L - T) - t` and
`2n - s`; the bounds `s ≤ 2n` and `t ≥ L - T` of `root_bounds` keep it in the closed rectangle; `omega` closes the grade check. -/
theorem freeV_reflect_even (frame : ChildFrame) {x y : ℤ} (hz : (x, y) ∈ frame.freeV) (hp : (x + y) % 2 = 0) :
    (frame.child.num - frame.child.den + 1 - x, frame.child.num + frame.child.den - 1 - y) ∈ frame.freeV := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := frame.child_num_odd
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have hT2 := FreeVCutExist.periodDenominator_even frame
  have hevz : EvenSite (x, y) := by unfold EvenSite; show (x + y) % 2 = 0; exact hp
  have hsl := (frame.root_bounds hz hevz).2.1
  have hlo := (frame.root_bounds hz hevz).2.2.1
  have htp : frame.tGrade (x, y) % 2 = 0 := by
    have h := FanInputs.tGrade_mod_two frame (x, y)
    rw [h]; exact hp
  have eE : EvenSite (frame.child.num - frame.child.den + 1 - x, frame.child.num + frame.child.den - 1 - y) := by
    unfold EvenSite
    show ((frame.child.num - frame.child.den + 1 - x) + (frame.child.num + frame.child.den - 1 - y)) % 2 = 0
    omega
  have oW : ¬ EvenSite (frame.child.num - frame.child.den + 1 - x - 1,
      frame.child.num + frame.child.den - 1 - y) := by
    unfold EvenSite
    show ¬ ((frame.child.num - frame.child.den + 1 - x - 1 + (frame.child.num + frame.child.den - 1 - y)) % 2 = 0)
    omega
  have oZW : ¬ EvenSite (x - 1, y) := by unfold EvenSite; show ¬ ((x - 1 + y) % 2 = 0); omega
  rw [FreeCutSucc.mem_freeV_iff] at hz ⊢
  simp only [closedRect, if_pos hevz, if_neg oZW, if_pos eE, if_neg oW, ChildFrame.vSpectrum, sGrade_eq_w1s] at hz ⊢
  simp only [w1t_refl, w1s_refl, w1t_refl_west, w1s_refl_west]
  simp only [tGrade_eq_w1t, sGrade_eq_w1s, frame_periodDenominator_eq] at hsl hlo htp hT2
  generalize w1t frame.child.num frame.child.den (x, y) = t at *
  generalize w1s frame.child.num frame.child.den (x, y) = s at *
  generalize w1T frame.child.num frame.child.den = T at *
  omega

/-- **The reflection `z ↦ vLast - z` preserves the free V cut, from an odd site** (the lower bound `t ≥ 2d + n − T` is the input). -/
theorem freeV_reflect_odd (frame : ChildFrame) {x y : ℤ} (hz : (x, y) ∈ frame.freeV) (hp : (x + y) % 2 = 1)
    (hlo : 2 * frame.child.den + frame.child.num - frame.child.periodDenominator ≤ frame.tGrade (x, y))
    (hT2 : frame.child.periodDenominator % 2 = 0) :
    (frame.child.num - frame.child.den + 1 - x, frame.child.num + frame.child.den - 1 - y) ∈ frame.freeV := by
  obtain ⟨hn0, hnd, hdn, hd3, hP⟩ := frame.child_facts
  have hnodd : frame.child.num % 2 = 1 := frame.child_num_odd
  have hev : (frame.child.num + frame.child.den) % 2 = 0 := frame.child_even
  have hdodd : frame.child.den % 2 = 1 := by omega
  have htp : frame.tGrade (x, y) % 2 = 1 := by
    have h := FanInputs.tGrade_mod_two frame (x, y)
    rw [h]; exact hp
  have oZ : ¬ EvenSite (x, y) := by unfold EvenSite; show ¬ ((x + y) % 2 = 0); omega
  have oE : ¬ EvenSite (frame.child.num - frame.child.den + 1 - x, frame.child.num + frame.child.den - 1 - y) := by
    unfold EvenSite
    show ¬ ((frame.child.num - frame.child.den + 1 - x + (frame.child.num + frame.child.den - 1 - y)) % 2 = 0)
    omega
  have eW : EvenSite (frame.child.num - frame.child.den + 1 - x - 1,
      frame.child.num + frame.child.den - 1 - y) := by
    unfold EvenSite
    show ((frame.child.num - frame.child.den + 1 - x - 1 + (frame.child.num + frame.child.den - 1 - y)) % 2 = 0)
    omega
  have eZW : EvenSite (x - 1, y) := by unfold EvenSite; show (x - 1 + y) % 2 = 0; omega
  rw [FreeCutSucc.mem_freeV_iff] at hz ⊢
  simp only [closedRect, if_neg oZ, if_pos eZW, if_neg oE, if_pos eW, ChildFrame.vSpectrum, sGrade_eq_w1s] at hz ⊢
  simp only [w1t_refl, w1s_refl, w1t_refl_west, w1s_refl_west]
  simp only [tGrade_eq_w1t, frame_periodDenominator_eq] at hlo hT2 htp
  generalize w1t frame.child.num frame.child.den (x, y) = t at *
  generalize w1s frame.child.num frame.child.den (x, y) = s at *
  generalize w1T frame.child.num frame.child.den = T at *
  omega

/-- **The free V cut is invariant under `z ↦ vLast - z`.** -/
theorem freeV_reflect (frame : ChildFrame) {x y : ℤ} (hz : (x, y) ∈ frame.freeV) :
    (frame.child.num - frame.child.den + 1 - x, frame.child.num + frame.child.den - 1 - y) ∈ frame.freeV := by
  have hT2 := FreeVCutExist.periodDenominator_even frame
  rcases Int.emod_two_eq_zero_or_one (x + y) with hp | hp
  · exact freeV_reflect_even frame hz hp
  · have hodd : ¬ EvenSite (x, y) := by unfold EvenSite; show ¬ ((x + y) % 2 = 0); omega
    have hlo := VOddLower.odd_lower_of_mem frame hz hodd
    exact freeV_reflect_odd frame hz hp hlo hT2

/-- **The V predecessor exists off `vFirst`**: reflect, take the successor, reflect back. -/
theorem freeV_pred_exists (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV)
    (hne : z ≠ FLatticePaper.Induction.vFirst) :
    (z.1, z.2 - 1) ∈ frame.freeV ∨ (z.1 + 1, z.2 - 1) ∈ frame.freeV := by
  obtain ⟨x, y⟩ := z
  have hw := freeV_reflect frame hz
  have hwne : (frame.child.num - frame.child.den + 1 - x, frame.child.num + frame.child.den - 1 - y) ≠
      frame.vLast := by
    intro h
    apply hne
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [ChildFrame.vLast] at h1 h2
    exact Prod.ext (by simp only [FLatticePaper.Induction.vFirst]; omega)
      (by simp only [FLatticePaper.Induction.vFirst]; omega)
  rcases FreeVCutExist.freeV_succ_exists frame hw hwne with h | h
  · have hr := freeV_reflect frame h
    left
    convert hr using 2 <;> omega
  · have hr := freeV_reflect frame h
    right
    convert hr using 2 <;> omega

end FLatticePaper.FreeCutPred
