import FLatticePaper.Plane.Induction.FreeTraceBox
import FLatticePaper.Plane.Induction.ShortPassages

/-! Task 72 (route restatements, option (b) of the lead): H_EN and V_NW take their step hypothesis instead of the windows.

This module: the odd free V box `1 − c ≤ x ≤ 0`, `1 ≤ y ≤ L − 2` (integer form `vbox_odd`, extraction `freeV_odd_box`). -/

namespace FLatticePaper.Induction

namespace RouteSteps

open ShortPassages FreeTraceBox

/-- The odd free V box in integer coordinates, with `L = D + N`, `c = D − N`, `T = D² + 2DN − N²`. -/
theorem vbox_odd (N D x y : ℤ) (hN : 1 ≤ N) (hND : N + 2 ≤ D)
    (hE1 : N - (D ^ 2 + 2 * D * N - N ^ 2) ≤ N * x - D * y) (hE2 : N * x - D * y ≤ D)
    (hE3 : 2 - (D - N) ≤ (D + N) * x + (D - N) * y)
    (hV : (D + N) * x + (D - N) * y ≤ (D + N) - 2) (hpar : (x + y) % 2 = 1) :
    1 - (D - N) ≤ x ∧ x ≤ 0 ∧ 1 ≤ y ∧ y ≤ (D + N) - 2 := by
  have hx0 : x ≤ 0 := by
    by_contra h
    have hy : y ≤ -1 := by
      by_contra h2
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ D - N by omega) (show (0 : ℤ) ≤ y by omega),
        mul_nonneg (show (0 : ℤ) ≤ D + N by omega) (show (0 : ℤ) ≤ x - 1 by omega)]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ N by omega) (show (0 : ℤ) ≤ x - 1 by omega),
      mul_nonneg (show (0 : ℤ) ≤ D by omega) (show (0 : ℤ) ≤ -1 - y by omega)]
  have hy1 : 1 ≤ y := by
    by_contra h
    rcases lt_or_eq_of_le hx0 with hx | hx
    · nlinarith [mul_nonneg (show (0 : ℤ) ≤ D + N by omega) (show (0 : ℤ) ≤ -1 - x by omega),
        mul_nonneg (show (0 : ℤ) ≤ D - N by omega) (show (0 : ℤ) ≤ -y by omega)]
    · subst hx
      have hy' : y ≤ -1 := by omega
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ D - N by omega) (show (0 : ℤ) ≤ -1 - y by omega)]
  have hyL : y ≤ (D + N) - 2 := by
    by_contra h
    rcases (show y = (D + N) - 1 ∨ (D + N) ≤ y by omega) with hy | hy
    · subst hy
      have hxa : x ≤ 1 - (D - N) := by
        by_contra h'
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ D + N by omega) (show (0 : ℤ) ≤ x - (2 - (D - N)) by omega)]
      have hxb : 1 - (D - N) ≤ x := by
        by_contra h'
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ D + N by omega) (show (0 : ℤ) ≤ -(D - N) - x by omega)]
      omega
    · have hxc : x < 1 - (D - N) := by
        by_contra h'
        nlinarith [mul_nonneg (show (0 : ℤ) ≤ D + N by omega) (show (0 : ℤ) ≤ x - (1 - (D - N)) by omega),
          mul_nonneg (show (0 : ℤ) ≤ D - N by omega) (show (0 : ℤ) ≤ y - (D + N) by omega)]
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ D by omega) (show (0 : ℤ) ≤ y - (D + N) by omega),
        mul_nonneg (show (0 : ℤ) ≤ N by omega) (show (0 : ℤ) ≤ -(D - N) - x by omega)]
  have hxa : 1 - (D - N) ≤ x := by
    by_contra h'
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ D + N by omega) (show (0 : ℤ) ≤ -(D - N) - x by omega),
      mul_nonneg (show (0 : ℤ) ≤ D - N by omega) (show (0 : ℤ) ≤ (D + N) - 2 - y by omega)]
  exact ⟨hxa, hx0, hy1, hyL⟩

/-- The free V trace on odd sites lies in the box `1 − c ≤ x ≤ 0`, `1 ≤ y ≤ L − 2`. -/
theorem freeV_odd_box (frame : ChildFrame) {x y : ℤ} (hz : (x, y) ∈ frame.freeV) (hodd : ¬ EvenSite (x, y)) :
    1 - (frame.child.den - frame.child.num) ≤ x ∧ x ≤ 0 ∧ 1 ≤ y ∧
      y ≤ frame.child.num + frame.child.den - 2 := by
  have hz' := hz
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hz'
  obtain ⟨hcl, -, hsp⟩ := hz'
  rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_neg hodd] at hcl
  obtain ⟨hE1, hE2, hE3, -⟩ := hcl
  obtain ⟨hTd, hN0, hND, -⟩ := period_facts frame
  have hodd' : ¬ ((x + y) % 2 = 0) := hodd
  have hV : frame.sGrade (x, y) ≤ frame.child.den + frame.child.num - 2 := by
    unfold ChildFrame.vSpectrum at hsp
    obtain ⟨-, hsp2⟩ := hsp
    rcases hsp2 with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have ht : frame.tGrade (x, y) = frame.child.num * x - frame.child.den * y := rfl
  have hs : frame.sGrade (x, y) =
      (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y := rfl
  have hN1 : 1 ≤ frame.child.num := by omega
  obtain ⟨a, b, c, e⟩ := vbox_odd frame.child.num frame.child.den x y hN1 hND
    (by linarith) (by linarith) (by linarith) (by linarith) (by omega)
  exact ⟨a, b, c, by omega⟩

/-- For an even free H site the `s` window of `H_EN_middle_nonfree` holds: `s < T + 2 − 2d`. By the H box, `x ≤ d` and `y ≤ n − 1`;
`s ≥ T + 2 − 2d` forces `x = d`, and then `t = d (n − y)` is even only if `y ≠ n − 1`, which the bound `t ≤ L − 2` forbids. -/
theorem freeH_even_s_lt (frame : ChildFrame) {x y : ℤ} (hz : (x, y) ∈ frame.freeH) (hev : EvenSite (x, y)) :
    frame.sGrade (x, y) < frame.child.periodDenominator + 2 - 2 * frame.child.den := by
  have hbox : 1 ≤ x ∧ x ≤ frame.child.den ∧ 0 ≤ y ∧ y ≤ frame.child.num - 1 := freeH_box frame hz
  obtain ⟨hx1, hxd, hy0, hyn⟩ := hbox
  have hz' := hz
  simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz'
  obtain ⟨hcl, -, hsp⟩ := hz'
  rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_pos hev] at hcl
  obtain ⟨hE1, hE2, hE3, hE4⟩ := hcl
  obtain ⟨hTd, hN0, hND, -⟩ := period_facts frame
  have hpar : frame.tGrade (x, y) % 2 = (x + y) % 2 := FLatticePaper.Induction.tGrade_parity frame (x, y)
  have hpar' : (x + y) % 2 = 0 := hev
  have hodd := (FLatticePaper.W1Exit.child_parity frame).2
  have ht : frame.tGrade (x, y) = frame.child.num * x - frame.child.den * y := rfl
  have hs : frame.sGrade (x, y) =
      (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y := rfl
  by_contra h
  rw [not_lt] at h
  have hLx : (frame.child.den + frame.child.num) * (frame.child.den - 1) <
      (frame.child.den + frame.child.num) * x := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.den - frame.child.num by omega)
      (show (0 : ℤ) ≤ frame.child.num - 1 - y by omega)]
  have hxgt : frame.child.den - 1 < x := lt_of_mul_lt_mul_left hLx (by omega)
  have hxeq : x = frame.child.den := by omega
  subst hxeq
  have hyk : y = frame.child.num - 1 := by
    by_contra hne
    have hy2 : y ≤ frame.child.num - 2 := by omega
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.den by omega)
      (show (0 : ℤ) ≤ frame.child.num - 2 - y by omega)]
  have htD : frame.tGrade (frame.child.den, y) = frame.child.den := by
    rw [ht, hyk]
    ring
  omega

/-- **H_EN with the step hypothesis (option (b)).** An even free H root whose E-step `z + (1,0)` is not a free H site has a nonfree
middle `z + (1,0)`. The window `c + 2 ≤ t(z)` of `H_EN_middle_nonfree` holds: if `t(z) ≤ c`, then the E-step is a free H site
(its `t` is `t + n ≤ d`, odd, its `s` is in the odd range since `s ≤ T − 2` by the box, and its lower neighbour is off the even branch). -/
theorem H_EN_of_step (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeH) (hev : EvenSite z)
    (hstep : z + (1, 0) ∉ frame.freeH) : Nonfree frame (z + (1, 0)) := by
  obtain ⟨x, y⟩ := z
  have hS := freeH_even_s_lt frame hz hev
  have hcl : (x, y) ∈ frame.closedPolygon := by
    have hz' := hz
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz'
    exact hz'.1
  have hT : frame.child.den - frame.child.num + 2 ≤ frame.tGrade (x, y) := by
    by_contra h
    rw [not_le] at h
    apply hstep
    have hm : ((x, y) : Site) + ((1 : ℤ), (0 : ℤ)) = (x + 1, y) := by
      ext <;> simp
    rw [hm]
    have hbox : 1 ≤ x ∧ x ≤ frame.child.den ∧ 0 ≤ y ∧ y ≤ frame.child.num - 1 := freeH_box frame hz
    obtain ⟨hx1, hxd, hy0, hyn⟩ := hbox
    have hz' := hz
    simp only [ChildFrame.freeH, Set.mem_setOf_eq] at hz'
    obtain ⟨hcl0, -, hsp⟩ := hz'
    rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_pos hev] at hcl0
    obtain ⟨hE1, hE2, hE3, hE4⟩ := hcl0
    obtain ⟨hTd, hN0, hND, hD3⟩ := period_facts frame
    have hpar : frame.tGrade (x, y) % 2 = (x + y) % 2 :=
      FLatticePaper.Induction.tGrade_parity frame (x, y)
    have hpar' : (x + y) % 2 = 0 := hev
    have hodd2 := (FLatticePaper.W1Exit.child_parity frame).1
    have hodd := (FLatticePaper.W1Exit.child_parity frame).2
    have ht : frame.tGrade (x, y) = frame.child.num * x - frame.child.den * y := rfl
    have hs : frame.sGrade (x, y) =
        (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y := rfl
    have htm : frame.tGrade (x + 1, y) = frame.tGrade (x, y) + frame.child.num := by
      rw [ht]
      show frame.child.num * (x + 1) - frame.child.den * y =
        frame.child.num * x - frame.child.den * y + frame.child.num
      ring
    have hsm : frame.sGrade (x + 1, y) = frame.sGrade (x, y) + (frame.child.den + frame.child.num) := by
      rw [hs]
      show (frame.child.den + frame.child.num) * (x + 1) + (frame.child.den - frame.child.num) * y =
        (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y +
          (frame.child.den + frame.child.num)
      ring
    have hc2 : (frame.child.den - frame.child.num) % 2 = 0 := by omega
    have hT0 : 0 ≤ frame.child.periodDenominator := by
      rw [hTd]
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.den - frame.child.num by omega)
        (show (0 : ℤ) ≤ frame.child.den + frame.child.num by omega),
        mul_nonneg (show (0 : ℤ) ≤ frame.child.den by omega) (show (0 : ℤ) ≤ frame.child.num by omega)]
    have hsT : frame.sGrade (x, y) ≤ frame.child.periodDenominator - 2 := by
      rw [hs]
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.den + frame.child.num by omega)
        (show (0 : ℤ) ≤ frame.child.den - x by omega),
        mul_nonneg (show (0 : ℤ) ≤ frame.child.den - frame.child.num by omega)
        (show (0 : ℤ) ≤ frame.child.num - 1 - y by omega)]
    have ht2 : 2 ≤ frame.tGrade (x, y) := by
      unfold ChildFrame.hSpectrum at hsp
      rcases hsp with ⟨-, h1, -⟩ | ⟨h1, -, -⟩
      · exact h1
      · omega
    have htc : frame.tGrade (x, y) ≤ frame.child.den - frame.child.num := by omega
    have hEodd : ¬ EvenSite (x + 1, y) := by
      show ¬ ((x + 1 + y) % 2 = 0)
      omega
    simp only [ChildFrame.freeH, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_neg hEodd, htm, hsm]
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    · show (x + 1, y - 1) ∉ frame.closedPolygon
      intro hm2
      have hEev2 : EvenSite (x + 1, y - 1) := by
        show (x + 1 + (y - 1)) % 2 = 0
        omega
      rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_pos hEev2] at hm2
      obtain ⟨-, hm3, -, -⟩ := hm2
      have htm2 : frame.tGrade (x + 1, y - 1) =
          frame.tGrade (x, y) + (frame.child.den + frame.child.num) := by
        rw [ht]
        show frame.child.num * (x + 1) - frame.child.den * (y - 1) =
          frame.child.num * x - frame.child.den * y + (frame.child.den + frame.child.num)
        ring
      rw [htm2] at hm3
      linarith
    · show frame.hSpectrum (frame.tGrade (x + 1, y))
      rw [htm]
      unfold ChildFrame.hSpectrum
      right
      exact ⟨by omega, by omega, by omega⟩
  have key := H_EN_middle_nonfree frame (x, y) hev hcl hT hS
  exact key

/-- **V_NW with the step hypothesis (option (b)).** An odd free V root whose N-step `z + (0,1)` is not a free V site has a nonfree
middle `z + (0,1)`. The window `2n + 2 − c ≤ s(z)` of `V_NW_middle_nonfree` holds: if `s(z) < 2n + 2 − c`, the N-step is a free V
site (its `s` is `s + c ≤ 2n`, and its right neighbour `z + (−1, 1)` has `s − 2n < 2 − c`, so it is off the odd branch). The other
two window bounds hold on every odd free V site by `freeV_odd_box`. -/
theorem V_NW_of_step (frame : ChildFrame) {z : Site} (hz : z ∈ frame.freeV) (hodd : ¬ EvenSite z)
    (hstep : z + (0, 1) ∉ frame.freeV) : Nonfree frame (z + (0, 1)) := by
  obtain ⟨x, y⟩ := z
  have hm : ((x, y) : Site) + ((0 : ℤ), (1 : ℤ)) = (x, y + 1) := by
    ext <;> simp
  obtain ⟨hx1, hx2, hy1, hy2⟩ := freeV_odd_box frame hz hodd
  have hz' := hz
  simp only [ChildFrame.freeV, Set.mem_setOf_eq] at hz'
  obtain ⟨hcl, -, hsp⟩ := hz'
  rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_neg hodd] at hcl
  obtain ⟨hE1, hE2, hE3, -⟩ := hcl
  obtain ⟨hTd, hN0, hND, hD3⟩ := period_facts frame
  have hodd' : ¬ ((x + y) % 2 = 0) := hodd
  have hodd2 := (FLatticePaper.W1Exit.child_parity frame).1
  have hodd3 := (FLatticePaper.W1Exit.child_parity frame).2
  have ht : frame.tGrade (x, y) = frame.child.num * x - frame.child.den * y := rfl
  have hs : frame.sGrade (x, y) =
      (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y := rfl
  have hsp' := hsp
  unfold ChildFrame.vSpectrum at hsp'
  obtain ⟨hsEven, hsp2⟩ := hsp'
  have hV : frame.sGrade (x, y) ≤ frame.child.den + frame.child.num - 2 := by
    rcases hsp2 with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
  have hc2 : (frame.child.den - frame.child.num) % 2 = 0 := by omega
  have hT0 : 0 ≤ frame.child.periodDenominator := by
    rw [hTd]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.den - frame.child.num by omega)
      (show (0 : ℤ) ≤ frame.child.den + frame.child.num by omega),
      mul_nonneg (show (0 : ℤ) ≤ frame.child.den by omega) (show (0 : ℤ) ≤ frame.child.num by omega)]
  have htm : frame.tGrade (x, y + 1) = frame.tGrade (x, y) - frame.child.den := by
    rw [ht]
    show frame.child.num * x - frame.child.den * (y + 1) =
      frame.child.num * x - frame.child.den * y - frame.child.den
    ring
  have hsc : frame.sGrade (x, y + 1) = frame.sGrade (x, y) + (frame.child.den - frame.child.num) := by
    rw [hs]
    show (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * (y + 1) =
      (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y +
        (frame.child.den - frame.child.num)
    ring
  have hS1 : 2 * frame.child.num + 2 - (frame.child.den - frame.child.num) ≤ frame.sGrade (x, y) := by
    by_contra h
    rw [not_le] at h
    apply hstep
    rw [hm]
    have hEv : EvenSite (x, y + 1) := by
      show (x + (y + 1)) % 2 = 0
      omega
    have hEodd2 : ¬ EvenSite (x - 1, y + 1) := by
      show ¬ ((x - 1 + (y + 1)) % 2 = 0)
      omega
    simp only [ChildFrame.freeV, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_⟩
    · rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_pos hEv, htm, hsc]
      refine ⟨?_, ?_, ?_, ?_⟩
      · nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.num by omega)
          (show (0 : ℤ) ≤ x - (1 - (frame.child.den - frame.child.num)) by omega),
          mul_nonneg (show (0 : ℤ) ≤ frame.child.den by omega)
          (show (0 : ℤ) ≤ (frame.child.den + frame.child.num) - 2 - y by omega)]
      · omega
      · omega
      · omega
    · show (x - 1, y + 1) ∉ frame.closedPolygon
      intro hm2
      rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_neg hEodd2] at hm2
      obtain ⟨-, -, h3, -⟩ := hm2
      have hsm2 : frame.sGrade (x - 1, y + 1) = frame.sGrade (x, y) - 2 * frame.child.num := by
        rw [hs]
        show (frame.child.den + frame.child.num) * (x - 1) + (frame.child.den - frame.child.num) * (y + 1) =
          (frame.child.den + frame.child.num) * x + (frame.child.den - frame.child.num) * y -
            2 * frame.child.num
        ring
      rw [hsm2] at h3
      omega
    · show frame.vSpectrum (frame.sGrade (x, y + 1))
      rw [hsc]
      unfold ChildFrame.vSpectrum
      exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩
  have ht1 : frame.child.num + frame.child.den - 1 - frame.child.periodDenominator + frame.child.den <
      frame.tGrade (x, y) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.num by omega)
      (show (0 : ℤ) ≤ x - (1 - (frame.child.den - frame.child.num)) by omega),
      mul_nonneg (show (0 : ℤ) ≤ frame.child.den by omega)
      (show (0 : ℤ) ≤ (frame.child.den + frame.child.num) - 2 - y by omega)]
  have ht2 : frame.tGrade (x, y) < frame.child.den := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.num by omega) (show (0 : ℤ) ≤ -x by omega),
      mul_nonneg (show (0 : ℤ) ≤ frame.child.den by omega) (show (0 : ℤ) ≤ y - 1 by omega)]
  exact V_NW_middle_nonfree frame (x, y) hodd hS1 hV ht1 ht2

end RouteSteps

end FLatticePaper.Induction
