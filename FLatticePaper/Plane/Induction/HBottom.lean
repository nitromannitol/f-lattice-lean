import FLatticePaper.Plane.Induction.HEnum
import FLatticePaper.Plane.Induction.ArcPsi

/-! Task w3, step A: the bottom of the free H arc is fixed, `H 0 = (1,0)` and `H 1 = (2,0)`, for every child frame.

Both points are free H points by the explicit polygon inequalities (`closedPolygon`, `hSpectrum`), and the arc is one point per
abscissa (`freeH_abscissa_unique`). So any enumeration of the arc with abscissae `j + 1` starts at `(1,0)` and `(2,0)`. -/

namespace FLatticePaper.HBottom

open Farey FLatticePaper FLatticePaper.Induction

theorem one_zero_mem (frame : ChildFrame) : ((1 : ℤ), (0 : ℤ)) ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  have hT2 : 2 ≤ frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  have ht : frame.tGrade ((1 : ℤ), (0 : ℤ)) = frame.child.num := by
    unfold ChildFrame.tGrade
    ring
  have ht' : frame.tGrade ((1 : ℤ), (-1 : ℤ)) = frame.child.num + frame.child.den := by
    unfold ChildFrame.tGrade
    ring
  have hev : EvenSite ((1 : ℤ), (-1 : ℤ)) := by
    unfold EvenSite
    norm_num
  have hodd : ¬ EvenSite ((1 : ℤ), (0 : ℤ)) := by
    unfold EvenSite
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · unfold ChildFrame.closedPolygon
    simp only [Set.mem_setOf_eq]
    rw [if_neg hodd]
    have hs : frame.sGrade ((1 : ℤ), (0 : ℤ)) = frame.child.den + frame.child.num := by
      unfold ChildFrame.sGrade
      ring
    rw [ht, hs]
    refine ⟨by omega, by omega, by omega, by omega⟩
  · show ((1 : ℤ), ((0 : ℤ) - 1)) ∉ frame.closedPolygon
    intro hmem
    have hm : ((1 : ℤ), ((0 : ℤ) - 1)) ∈ frame.closedPolygon := hmem
    unfold ChildFrame.closedPolygon at hm
    simp only [Set.mem_setOf_eq] at hm
    rw [if_pos (by unfold EvenSite; norm_num)] at hm
    have h2 : frame.tGrade ((1 : ℤ), ((0 : ℤ) - 1)) = frame.child.num + frame.child.den := by
      unfold ChildFrame.tGrade
      ring
    have := hm.2.1
    rw [h2] at this
    omega
  · unfold ChildFrame.hSpectrum
    rw [ht]
    rcases Int.emod_two_eq_zero_or_one frame.child.num with h | h
    · left
      exact ⟨h, by omega, by omega⟩
    · right
      exact ⟨h, le_refl _, by omega⟩

theorem two_zero_mem (frame : ChildFrame) : ((2 : ℤ), (0 : ℤ)) ∈ frame.freeH := by
  obtain ⟨hn0, hnd, hdn, hd3, hT⟩ := frame.child_facts
  have hT2 : 2 ≤ frame.child.periodDenominator := by
    rw [hT]
    nlinarith
  have ht : frame.tGrade ((2 : ℤ), (0 : ℤ)) = 2 * frame.child.num := by
    unfold ChildFrame.tGrade
    ring
  have hs : frame.sGrade ((2 : ℤ), (0 : ℤ)) = 2 * (frame.child.den + frame.child.num) := by
    unfold ChildFrame.sGrade
    ring
  have hev : EvenSite ((2 : ℤ), (0 : ℤ)) := by
    unfold EvenSite
    norm_num
  have hodd : ¬ EvenSite ((2 : ℤ), ((0 : ℤ) - 1)) := by
    unfold EvenSite
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · unfold ChildFrame.closedPolygon
    simp only [Set.mem_setOf_eq]
    rw [if_pos hev]
    rw [ht, hs]
    refine ⟨by omega, by omega, by omega, ?_⟩
    rw [hT]
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ frame.child.den - frame.child.num by omega)
        (show (0 : ℤ) ≤ frame.child.den + frame.child.num by omega),
      mul_nonneg (show (0 : ℤ) ≤ frame.child.den by omega) (show (0 : ℤ) ≤ frame.child.num - 1 by omega)]
  · show ((2 : ℤ), ((0 : ℤ) - 1)) ∉ frame.closedPolygon
    intro hmem
    have hm : ((2 : ℤ), ((0 : ℤ) - 1)) ∈ frame.closedPolygon := hmem
    unfold ChildFrame.closedPolygon at hm
    simp only [Set.mem_setOf_eq] at hm
    rw [if_neg hodd] at hm
    have h2 : frame.tGrade ((2 : ℤ), ((0 : ℤ) - 1)) = 2 * frame.child.num + frame.child.den := by
      unfold ChildFrame.tGrade
      ring
    have := hm.2.1
    rw [h2] at this
    omega
  · unfold ChildFrame.hSpectrum
    rw [ht]
    left
    exact ⟨by omega, by omega, by omega⟩

/-- The enumeration of the free H arc has `H 0 = (1,0)`, given that its abscissa is `1`. -/
theorem H_zero_eq (frame : ChildFrame) {H : ℕ → Site} (hH : H 0 ∈ frame.freeH) (hx : (H 0).1 = 1) :
    H 0 = ((1 : ℤ), (0 : ℤ)) := by
  have e : H 0 = ((1 : ℤ), (H 0).2) := Prod.ext hx rfl
  have hy : (H 0).2 = 0 := by
    have h1 : ((1 : ℤ), (H 0).2) ∈ frame.freeH := e ▸ hH
    exact freeH_abscissa_unique frame h1 (one_zero_mem frame)
  rw [e, hy]

theorem H_one_eq (frame : ChildFrame) {H : ℕ → Site} (hH : H 1 ∈ frame.freeH) (hx : (H 1).1 = 2) :
    H 1 = ((2 : ℤ), (0 : ℤ)) := by
  have e : H 1 = ((2 : ℤ), (H 1).2) := Prod.ext hx rfl
  have hy : (H 1).2 = 0 := by
    have h1 : ((2 : ℤ), (H 1).2) ∈ frame.freeH := e ▸ hH
    exact freeH_abscissa_unique frame h1 (two_zero_mem frame)
  rw [e, hy]

end FLatticePaper.HBottom
