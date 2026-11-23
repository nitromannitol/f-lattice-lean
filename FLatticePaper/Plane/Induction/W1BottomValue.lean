import FLatticePaper.Plane.Induction.StrongPriceInputs
import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.W1Lower
import FLatticePaper.Plane.Induction.BaseGeometry

/-! # Task 72 (4): the bottom-arc value of the primitive price

On the bottom H arc the price takes the value `c₀` at `H₀ = (1, 0)` and `c₀ − 1` at the other bottom sites (numerically, on the
36 proper words of length at most 3).

Two facts are proved here, from the packet strips of the word's own field:
* `price_hFirst`: `P(H₀) = c₀`. The zero clause gives `F(H₀) = 0` (`t(H₀) = n`), and `s(H₀ − v) = s(H₀) − s(v) = d + n − 2` lies in the
  `h₀` clause window, so `F(H₀ − v) = h₀(H₀ − v)`; then `price_eq_cutPrice_sub_harmonic_of_zero` gives `P(H₀) = c₀ − h₀(H₀) = c₀`.
* `price_bottom_of_strip`: on any pure bottom site `z` whose shifted site `z − v` lies in the `h₀` clause window
  (`1 − 2d ≤ s(z − v) ≤ 2L − 1`), `P(z) = c₀ − h₀(z)`.

The remaining bottom sites are not covered by these windows (their `z − v`, and every representative `z − v + lV + kU` in the
window of the field's own strips, is outside them); their value needs the sheet analysis, which is not in this module. -/

namespace FLatticePaper.W1BottomValue

open Farey FLatticePaper FLatticePaper.Induction

/-- The shift of the `s`-grade is linear. -/
theorem sGrade_sub (frame : ChildFrame) (a b : Site) :
    frame.sGrade (a - b) = frame.sGrade a - frame.sGrade b := by
  unfold ChildFrame.sGrade
  simp only [Prod.fst_sub, Prod.snd_sub]
  ring

/-- **The H₀ value** (task 72 (4)): `P(1, 0) = c₀`. -/
theorem price_hFirst {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word)) :
    (frameAt word).price (standardField word) (1, 0) = (frameAt word).cutPrice := by
  have hpk := packet_of_strong h hS
  have hstr := hpk.strips
  obtain ⟨hn0, hnd, -, hd3, -⟩ := (frameAt word).child_facts
  have hF0 : standardField word (1, 0) = 0 :=
    hstr.1 (1, 0) (by simp only [ChildFrame.tGrade]; omega) (by simp only [ChildFrame.tGrade]; omega)
  have hs : (frameAt word).sGrade ((1, 0) - (frameAt word).parentShift) =
      (frameAt word).child.den + (frameAt word).child.num - 2 := by
    rw [sGrade_sub, FLatticePaper.W1Lower.sGrade_parentShift]
    unfold ChildFrame.sGrade
    simp only
    ring
  have h1 : standardField word ((1, 0) - (frameAt word).parentShift) =
      harmonicGrid ((1, 0) - (frameAt word).parentShift) :=
    hstr.2 _ (by rw [hs]; omega) (by rw [hs]; omega)
  have hv := FLatticePaper.StrongPriceInputs.price_eq_cutPrice_sub_harmonic_of_zero (frameAt word)
    (standardField word) (1, 0) hF0 h1
  have hh : harmonicGrid (1, 0) = 0 := by
    unfold harmonicGrid
    norm_num
  rw [hv, hh, sub_zero]

/-- **The strip class of the bottom arc**: on a pure bottom site `z` with `z − v` in the `h₀` clause window of the field,
`P(z) = c₀ − h₀(z)`. -/
theorem price_bottom_of_strip {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hS : StrongEstimates (conjWord word)) {z : Site}
    (hz : PureBottom (frameAt word).closedPolygon z)
    (hs1 : 1 - 2 * (frameAt word).child.den ≤ (frameAt word).sGrade (z - (frameAt word).parentShift))
    (hs2 : (frameAt word).sGrade (z - (frameAt word).parentShift) ≤
      2 * ((frameAt word).child.den + (frameAt word).child.num) - 1) :
    (frameAt word).price (standardField word) z = (frameAt word).cutPrice - harmonicGrid z := by
  have hpk := packet_of_strong h hS
  obtain ⟨hl, hr⟩ := (frameAt word).pureBottom_strip hz
  have hF0 : standardField word z = 0 := hpk.strips.1 z (by omega) (by omega)
  have h1 := hpk.strips.2 _ hs1 hs2
  exact FLatticePaper.StrongPriceInputs.price_eq_cutPrice_sub_harmonic_of_zero (frameAt word)
    (standardField word) z hF0 h1

end FLatticePaper.W1BottomValue
