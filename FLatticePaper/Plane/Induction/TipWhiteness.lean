import FLatticePaper.Plane.Induction.Q3White
import FLatticePaper.Plane.Induction.ShortPassages

/-! Task 72 (TIP_THEOREM, the whiteness hypotheses of the cut-tip escape).

Derived from the strips `ChildFrame.HasStrips F` and the tip grades `t(v) = −B`, `s(v) = 2ε` (the tip values are hypotheses here,
see `CanonicalDirections`):

* `laplacian_eq_zero_of_odd_strip`: an odd site whose vertical star lies in the harmonic s-strip is white;
* `W1_middle_white`: the W1 middle `v + (−1,0)` (`ε = +1`) is white (its star lies in the s-strip);
* `W1_root_freeV`, `W0_root_freeV`: the roots `v` (W1) and `v + (1,0)` (W0) are free V sites, hence white by
  `ChildFrame.laplacian_eq_zero_of_freeV`.

Not derived here: the whiteness of the W0 middle `v + (1,1)`. Its east input has `s = 3d + n − 2`, outside the harmonic s-strip
`[1 − 2d, 2L − 1]`, so it needs the two-sheet identity of TIP_THEOREM (the `fA`, `fC` evaluation). -/

namespace FLatticePaper.Induction

namespace TipWhiteness

open ShortPassages

/-- An odd site whose vertical star has its `s` values in the harmonic strip is white. -/
theorem laplacian_eq_zero_of_odd_strip (frame : ChildFrame) {F : Field} (hS : frame.HasStrips F) {u : Site}
    (hodd : ¬ EvenSite u)
    (hlo : 1 - 2 * frame.child.den ≤ frame.sGrade u - (frame.child.den - frame.child.num))
    (hhi : frame.sGrade u + (frame.child.den - frame.child.num) ≤ 2 * (frame.child.den + frame.child.num) - 1) :
    laplacian F u = 0 := by
  obtain ⟨-, -, hND, -⟩ := period_facts frame
  have hh := hS.2
  have hlap := harmonicGrid_harmonic u
  unfold laplacian at hlap ⊢
  simp only [incomingNeg, incomingPos, if_neg hodd] at hlap ⊢
  have h0 : F u = harmonicGrid u := hh u (by omega) (by omega)
  have h1 : F (u.1, u.2 - 1) = harmonicGrid (u.1, u.2 - 1) :=
    hh _ (by rw [frame.sGrade_sub_y u]; omega) (by rw [frame.sGrade_sub_y u]; omega)
  have h2 : F (u.1, u.2 + 1) = harmonicGrid (u.1, u.2 + 1) :=
    hh _ (by rw [frame.sGrade_add_y u]; omega) (by rw [frame.sGrade_add_y u]; omega)
  rw [h0, h1, h2]
  linarith

/-- **The W1 middle is white.** With `s(v) = 2` at the even tip vertex `v = (x, y)`, the middle `v + (−1,0)` has `s = 2 − L` and its
vertical star lies in the harmonic s-strip. -/
theorem W1_middle_white (frame : ChildFrame) {F : Field} (hS : frame.HasStrips F) {x y : ℤ}
    (hv : EvenSite (x, y)) (hs : frame.sGrade (x, y) = 2) :
    laplacian F (x - 1, y) = 0 := by
  have hv' : (x + y) % 2 = 0 := hv
  obtain ⟨-, hN0, hND, -⟩ := period_facts frame
  have hsm : frame.sGrade (x - 1, y) = frame.sGrade (x, y) - (frame.child.den + frame.child.num) := by
    rw [show frame.sGrade (x, y) = (frame.child.den + frame.child.num) * x +
        (frame.child.den - frame.child.num) * y from rfl]
    show (frame.child.den + frame.child.num) * (x - 1) + (frame.child.den - frame.child.num) * y = _
    ring
  apply laplacian_eq_zero_of_odd_strip frame hS
  · show ¬ ((x - 1 + y) % 2 = 0)
    omega
  · rw [hsm, hs]
    omega
  · rw [hsm, hs]
    omega

/-- **The W1 root is a free V site.** The tip vertex `v = (x, y)` is even with `t(v) = −B`, `s(v) = 2`. -/
theorem W1_root_freeV (frame : ChildFrame) {x y B : ℤ} (hv : EvenSite (x, y))
    (ht : frame.tGrade (x, y) = -B) (hs : frame.sGrade (x, y) = 2)
    (hB0 : 0 ≤ B) (hB2 : 5 * (frame.child.den + frame.child.num) ≤ frame.child.periodDenominator - B) :
    (x, y) ∈ frame.freeV := by
  have hv' : (x + y) % 2 = 0 := hv
  obtain ⟨hTd, hN0, hND, hD3⟩ := period_facts frame
  have hodd : ¬ EvenSite (x - 1, y) := by
    show ¬ ((x - 1 + y) % 2 = 0)
    omega
  have htm : frame.tGrade (x - 1, y) = frame.tGrade (x, y) - frame.child.num := by
    rw [show frame.tGrade (x, y) = frame.child.num * x - frame.child.den * y from rfl]
    show frame.child.num * (x - 1) - frame.child.den * y = _
    ring
  have hsm : frame.sGrade (x - 1, y) = frame.sGrade (x, y) - (frame.child.den + frame.child.num) := by
    rw [show frame.sGrade (x, y) = (frame.child.den + frame.child.num) * x +
        (frame.child.den - frame.child.num) * y from rfl]
    show (frame.child.den + frame.child.num) * (x - 1) + (frame.child.den - frame.child.num) * y = _
    ring
  simp only [ChildFrame.freeV, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_pos hv]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro hm
    rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_neg hodd, hsm, hs] at hm
    omega
  · unfold ChildFrame.vSpectrum
    rw [hs]
    exact ⟨by omega, Or.inl ⟨by omega, by omega⟩⟩

/-- **The W0 root is a free V site.** The tip vertex `v = (x, y)` is even with `t(v) = −B`, `s(v) = −2`; the root is `v + (1,0)`. -/
theorem W0_root_freeV (frame : ChildFrame) {x y B : ℤ} (hv : EvenSite (x, y))
    (ht : frame.tGrade (x, y) = -B) (hs : frame.sGrade (x, y) = -2)
    (hB0 : 0 ≤ B) (hB2 : 5 * (frame.child.den + frame.child.num) ≤ frame.child.periodDenominator - B) :
    (x + 1, y) ∈ frame.freeV := by
  have hv' : (x + y) % 2 = 0 := hv
  obtain ⟨hTd, hN0, hND, hD3⟩ := period_facts frame
  obtain ⟨hodd1, hodd2⟩ := FLatticePaper.W1Exit.child_parity frame
  have hodd : ¬ EvenSite (x + 1, y) := by
    show ¬ ((x + 1 + y) % 2 = 0)
    omega
  have htr : frame.tGrade (x + 1, y) = frame.tGrade (x, y) + frame.child.num := by
    rw [show frame.tGrade (x, y) = frame.child.num * x - frame.child.den * y from rfl]
    show frame.child.num * (x + 1) - frame.child.den * y = _
    ring
  have hsr : frame.sGrade (x + 1, y) = frame.sGrade (x, y) + (frame.child.den + frame.child.num) := by
    rw [show frame.sGrade (x, y) = (frame.child.den + frame.child.num) * x +
        (frame.child.den - frame.child.num) * y from rfl]
    show (frame.child.den + frame.child.num) * (x + 1) + (frame.child.den - frame.child.num) * y = _
    ring
  simp only [ChildFrame.freeV, Set.mem_setOf_eq]
  refine ⟨?_, ?_, ?_⟩
  · rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_neg hodd, htr, hsr]
    exact ⟨by omega, by omega, by omega, by omega⟩
  · intro hm
    have hm' : (x, y) ∈ frame.closedPolygon := by simpa using hm
    rw [FLatticePaper.Induction.mem_closedPolygon_iff, if_pos hv] at hm'
    obtain ⟨-, -, h3, -⟩ := hm'
    omega
  · unfold ChildFrame.vSpectrum
    rw [hsr, hs]
    exact ⟨by omega, Or.inr ⟨by omega, by omega⟩⟩

/-- **The W1 tip is white at both its root and its middle.** These are the whiteness hypotheses of `CutTipEscape.tip_W1_escape`. -/
theorem W1_tip_white (frame : ChildFrame) {F : Field} (hS : frame.HasStrips F) {x y B : ℤ} (hv : EvenSite (x, y))
    (ht : frame.tGrade (x, y) = -B) (hs : frame.sGrade (x, y) = 2)
    (hB0 : 0 ≤ B) (hB2 : 5 * (frame.child.den + frame.child.num) ≤ frame.child.periodDenominator - B) :
    laplacian F (x, y) = 0 ∧ laplacian F (x - 1, y) = 0 :=
  ⟨ChildFrame.laplacian_eq_zero_of_freeV frame hS (W1_root_freeV frame hv ht hs hB0 hB2),
    W1_middle_white frame hS hv hs⟩

/-- **The W0 root is white.** The W0 middle `v + (1,1)` is not covered here (see the module note). -/
theorem W0_tip_root_white (frame : ChildFrame) {F : Field} (hS : frame.HasStrips F) {x y B : ℤ} (hv : EvenSite (x, y))
    (ht : frame.tGrade (x, y) = -B) (hs : frame.sGrade (x, y) = -2)
    (hB0 : 0 ≤ B) (hB2 : 5 * (frame.child.den + frame.child.num) ≤ frame.child.periodDenominator - B) :
    laplacian F (x + 1, y) = 0 :=
  ChildFrame.laplacian_eq_zero_of_freeV frame hS (W0_root_freeV frame hv ht hs hB0 hB2)

end TipWhiteness

end FLatticePaper.Induction
