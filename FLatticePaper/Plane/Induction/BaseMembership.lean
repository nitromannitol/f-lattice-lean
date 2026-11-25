import FLatticePaper.Plane.Induction.BaseSpec
import FLatticePaper.Plane.Induction.ConjFreeH
import FLatticePaper.Plane.Induction.FreeVWindow
import FLatticePaper.Plane.Induction.Q3VStar
import FLatticePaper.Plane.Induction.SheetFacts
import FLatticePaper.Plane.Induction.NativeCases
import FLatticePaper.Plane.Induction.ZoneI1
import FLatticePaper.Plane.Induction.SheetOffsets

/-! Task 72 / Q31 psi (1), base membership: for a base point `z` of the word's free V cut, with ordinate `i = z₂` in the residue range,
`I − Z z = (1 + i, −z₁)` is a free H point of the conjugate.

The spectrum of the conjugate at `w = (1 + i, −x)` is `t_C(w) = p + c_p` (`BaseSpec`), the closed polygon of the conjugate is the
parametric `s_C` bound (`BaseSpec`), and the exit is `ConjFreeH.exit_of_hSpec`. -/

namespace FLatticePaper.BaseMembership

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.FreeVWindow

/-- **Base membership.** -/
theorem base_mem_freeH {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three) {z : Site}
    (hz : z ∈ (frameAt word).freeV) (hi : 0 ≤ z.2)
    (hir : z.2 ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 1)
    (hph : (frameAt word).eps = -1 ∨ z.2 ≤ (frameAt word).parents.odd.den + (frameAt word).parents.odd.num - 2) :
    (1 + z.2, -z.1) ∈ (frameAt (conjWord word)).freeH := by
  obtain ⟨hcn, hcd⟩ := FLatticePaper.Induction.frameAt_conj_num_den h
  have hpos : 0 < (frameAt word).parents.odd.num := frameAt_odd_num_pos h
  have hodd0 : ((frameAt word).parents.odd.num + (frameAt word).parents.odd.den) % 2 = 1 :=
    (frameAt word).valid.odd_parity
  obtain ⟨hDpos, hN0', hNle'⟩ := (frameAt word).valid.odd_bounds
  obtain ⟨hdq, hnq, -⟩ := (frameAt word).valid.even_bounds
  obtain ⟨hn0, hnd, hd2, hd3, -⟩ := (frameAt word).child_facts
  have hεdet : (frameAt word).eps = (frameAt word).parents.odd.num * (frameAt word).parents.even.den
      - (frameAt word).parents.odd.den * (frameAt word).parents.even.num :=
    FLatticePaper.SheetOffsets.eps_eq_det
  have hεd : (frameAt word).eps = (frameAt word).parents.odd.num * (frameAt word).child.den
      - (frameAt word).parents.odd.den * (frameAt word).child.num := by
    rw [hεdet, ZoneI1.child_den_eq (frameAt word), ZoneI1.child_num_eq (frameAt word)]
    ring
  have hε1 : (frameAt word).eps = 1 ∨ (frameAt word).eps = -1 := (frameAt word).eps_unit
  have hodd : ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) % 2 = 1 := by omega
  have hN1 : 1 ≤ (frameAt word).parents.odd.num := by omega
  have hNlt : (frameAt word).parents.odd.num < (frameAt word).parents.odd.den := by omega
  have hcd_eq : (frameAt word).child.den = 2 * (frameAt word).parents.odd.den + (frameAt word).parents.even.den :=
    ZoneI1.child_den_eq (frameAt word)
  have hcn_eq : (frameAt word).child.num = 2 * (frameAt word).parents.odd.num + (frameAt word).parents.even.num :=
    ZoneI1.child_num_eq (frameAt word)
  have hL : 2 * ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num)
      ≤ (frameAt word).child.den + (frameAt word).child.num := by
    omega
  set C := frameAt (conjWord word) with hCdef
  set w : Site := (1 + z.2, -z.1) with hwdef
  have hw1 : w.1 = 1 + z.2 := rfl
  have hw2 : w.2 = -z.1 := rfl
  have htw : C.tGrade w = ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * (1 + z.2)
      + ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * z.1 := by
    unfold ChildFrame.tGrade
    rw [hcn, hcd, hw1, hw2]
    ring
  have hsC : C.sGrade w = 2 * (frameAt word).parents.odd.den * (1 + z.2)
      - 2 * (frameAt word).parents.odd.num * z.1 := by
    unfold ChildFrame.sGrade
    rw [hcn, hcd, hw1, hw2]
    ring
  have hTC : C.child.periodDenominator = 2 * ((frameAt word).parents.odd.den ^ 2
      + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num - (frameAt word).parents.odd.num ^ 2) := by
    unfold Fraction.periodDenominator
    rw [hcn, hcd]
    ring
  have hpC := NativeCases.tGrade_parity C w
  have hcpos' : 0 < (frameAt word).child.den - (frameAt word).child.num := by omega
  show w ∈ C.closedPolygon ∧ (w.1, w.2 - 1) ∉ C.closedPolygon ∧ C.hSpectrum (C.tGrade w)
  have hTnn : 0 ≤ C.child.periodDenominator := by
    rw [hTC]
    have hDN : (frameAt word).parents.odd.num + 1 ≤ (frameAt word).parents.odd.den := by omega
    nlinarith
  by_cases hE : EvenSite z
  · -- even base: the conjugate point w is odd
    have hwodd : ¬ EvenSite w := by
      unfold EvenSite at hE ⊢
      rw [hw1, hw2]
      omega
    obtain ⟨hw0, hw1'⟩ := freeV_even_window (frameAt word) hz hE
    have hs0 : 0 ≤ ((frameAt word).child.den + (frameAt word).child.num) * z.1
        + ((frameAt word).child.den - (frameAt word).child.num) * z.2 := by
      unfold ChildFrame.sGrade at hw0
      exact hw0
    have hs1 : ((frameAt word).child.den + (frameAt word).child.num) * z.1
        + ((frameAt word).child.den - (frameAt word).child.num) * z.2 ≤ 2 * (frameAt word).child.num := by
      unfold ChildFrame.sGrade at hw1'
      exact hw1'
    obtain ⟨hp0, hp1⟩ := BaseSpec.even_base_range (frameAt word).parents.odd.den (frameAt word).parents.odd.num
      (frameAt word).child.num (frameAt word).child.den (frameAt word).eps z.1 z.2 hεd hε1 hN1 hNlt hodd hi
      hir hL hs0 hs1 hE
    have hsC' := BaseSpec.sC_even_bound (frameAt word).parents.odd.den (frameAt word).parents.odd.num
      (frameAt word).child.num (frameAt word).child.den (frameAt word).eps z.1 z.2 hεd hε1 hN1 hNlt hi hir hL
      (by omega) hs0 hs1
    have hsp : C.hSpectrum (C.tGrade w) := by
      unfold ChildFrame.hSpectrum
      rw [hcn, hcd]
      have hpC' : C.tGrade w % 2 = 1 := by
        rw [hpC, hw1, hw2]
        unfold EvenSite at hE
        omega
      have ht : C.tGrade w = ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * z.1
          + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * z.2
          + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
        rw [htw]
        ring
      right
      refine ⟨hpC', ?_, ?_⟩
      · linarith
      · linarith
    refine ⟨?_, ConjFreeH.exit_of_hSpec C w hsp, hsp⟩
    rw [FreeVWindow.mem_closedPolygon_odd C hwodd, htw, hsC, hcn, hcd, hTC]
    have hT' : 0 ≤ 2 * ((frameAt word).parents.odd.den ^ 2
        + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num - (frameAt word).parents.odd.num ^ 2) :=
      by rw [← hTC]; exact hTnn
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · linarith
    · linarith
    · linarith
    · linarith
  · -- odd base: the conjugate point w is even
    have hwev : EvenSite w := by
      unfold EvenSite at hE ⊢
      rw [hw1, hw2]
      omega
    obtain ⟨hw0, hw1'⟩ := freeV_odd_window (frameAt word) hz hE
    have hs0 : 2 - ((frameAt word).child.den - (frameAt word).child.num) ≤
        ((frameAt word).child.den + (frameAt word).child.num) * z.1
        + ((frameAt word).child.den - (frameAt word).child.num) * z.2 := by
      unfold ChildFrame.sGrade at hw0
      exact hw0
    have hs1 : ((frameAt word).child.den + (frameAt word).child.num) * z.1
        + ((frameAt word).child.den - (frameAt word).child.num) * z.2 ≤
        (frameAt word).child.den + (frameAt word).child.num - 2 := by
      unfold ChildFrame.sGrade at hw1'
      exact hw1'
    have hpar : (z.1 + z.2) % 2 = 1 := by
      unfold EvenSite at hE
      omega
    obtain ⟨hp0, hp1⟩ := BaseSpec.odd_base_range (frameAt word).parents.odd.den (frameAt word).parents.odd.num
      (frameAt word).child.num (frameAt word).child.den (frameAt word).eps z.1 z.2 hεd hε1 hN1 hNlt hodd hi
      hir hph hL hs0 hs1 hpar
    have hsC' := BaseSpec.sC_odd_bound (frameAt word).parents.odd.den (frameAt word).parents.odd.num
      (frameAt word).child.num (frameAt word).child.den (frameAt word).eps z.1 z.2 hεd hε1 hN1 hNlt hi hir hL
      hcpos' hs0 hs1
    obtain ⟨hsC0, hsC1⟩ := hsC'
    have hsp : C.hSpectrum (C.tGrade w) := by
      unfold ChildFrame.hSpectrum
      rw [hcn, hcd]
      have hpC' : C.tGrade w % 2 = 0 := by
        rw [hpC, hw1, hw2]
        unfold EvenSite at hE
        omega
      have ht : C.tGrade w = ((frameAt word).parents.odd.den + (frameAt word).parents.odd.num) * z.1
          + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) * z.2
          + ((frameAt word).parents.odd.den - (frameAt word).parents.odd.num) := by
        rw [htw]
        ring
      left
      refine ⟨hpC', ?_, ?_⟩
      · linarith
      · linarith
    refine ⟨?_, ConjFreeH.exit_of_hSpec C w hsp, hsp⟩
    rw [FreeVWindow.mem_closedPolygon_even C hwev, htw, hsC, hcn, hcd, hTC]
    have hT' : 0 ≤ 2 * ((frameAt word).parents.odd.den ^ 2
        + 2 * (frameAt word).parents.odd.den * (frameAt word).parents.odd.num - (frameAt word).parents.odd.num ^ 2) :=
      by rw [← hTC]; exact hTnn
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · linarith
    · linarith
    · linarith
    · linarith

end FLatticePaper.BaseMembership
