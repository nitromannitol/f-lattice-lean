import FLatticePaper.Plane.Induction.TieReduce
import FLatticePaper.Plane.Induction.W1MSheet

/-! Task 72 (hcollar, the black corner `(1, 1)`): at the bottom collar the corner `(1, 1)` is black.

The site `(1, 1)` is even with horizontal inputs `(0, 1)` and `(2, 1)`, both odd. On the child polygon the three sites lie in `E`,
where the sheet minimum `MW` agrees with the standard field (`standardField_eq_sheetMin_of_strong`). The standard strips of the
packet give `F(1,1) = 0` and `F(2,1) = 0` (both have `t` in the zero strip `[1 − d, n + 2d − 1]`), and `F(0,1) = h₀(0,1) = −1`
(`s(0,1) = d − n` lies in the harmonic strip). Hence `laplacian (MW word) (1, 1) = (−1 − 0) + (0 − 0) = −1`. -/

namespace FLatticePaper.Induction

open Farey FLatticePaper FLatticePaper.W1MSheet

/-- `h₀(0, 1) = −1`. -/
theorem harmonicGrid_zero_one : harmonicGrid (0, 1) = -1 := by
  unfold harmonicGrid
  norm_num

/-- The three sites `(0,1)`, `(1,1)`, `(2,1)` lie in the closed polygon of the word child. -/
theorem one_one_neighbourhood_mem (frame : ChildFrame) :
    ((0 : ℤ), (1 : ℤ)) ∈ frame.closedPolygon ∧ ((1 : ℤ), (1 : ℤ)) ∈ frame.closedPolygon ∧
      ((2 : ℤ), (1 : ℤ)) ∈ frame.closedPolygon := by
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := frame.child_facts
  have hT2 : frame.child.periodDenominator = frame.child.den ^ 2 + 2 * frame.child.den * frame.child.num -
      frame.child.num ^ 2 := hT
  refine ⟨?_, ?_, ?_⟩
  · rw [frame.mem_closedPolygon_iff]
    right
    refine ⟨by unfold EvenSite; norm_num, ?_, ?_, ?_, ?_⟩
    · unfold ChildFrame.tGrade
      rw [hT2]
      nlinarith
    · unfold ChildFrame.tGrade
      nlinarith
    · unfold ChildFrame.sGrade
      nlinarith
    · unfold ChildFrame.sGrade
      rw [hT2]
      nlinarith
  · rw [frame.mem_closedPolygon_iff]
    left
    refine ⟨by unfold EvenSite; norm_num, ?_, ?_, ?_, ?_⟩
    · unfold ChildFrame.tGrade
      rw [hT2]
      nlinarith
    · unfold ChildFrame.tGrade
      nlinarith
    · unfold ChildFrame.sGrade
      nlinarith
    · unfold ChildFrame.sGrade
      rw [hT2]
      nlinarith
  · rw [frame.mem_closedPolygon_iff]
    right
    refine ⟨by unfold EvenSite; norm_num, ?_, ?_, ?_, ?_⟩
    · unfold ChildFrame.tGrade
      rw [hT2]
      nlinarith
    · unfold ChildFrame.tGrade
      nlinarith
    · unfold ChildFrame.sGrade
      nlinarith
    · unfold ChildFrame.sGrade
      rw [hT2]
      nlinarith

/-- **The corner `(1, 1)` is black.** For every word, `laplacian (MW word) (1, 1) = −1`. -/
theorem laplacian_MW_one_one {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) :
    laplacian (MW word) (1, 1) = -1 := by
  have hP := packet_of_strong h hSE
  have hS := hP.strips
  obtain ⟨m01, m11, m21⟩ := one_one_neighbourhood_mem (frameAt word)
  obtain ⟨hn0, hnd, hd2, hd3, hT⟩ := (frameAt word).child_facts
  have hE : EvenSite ((1 : ℤ), (1 : ℤ)) := by unfold EvenSite; norm_num
  have eMW : ∀ z ∈ (frameAt word).closedPolygon, MW word z = standardField word z :=
    fun z hz => (standardField_eq_sheetMin_of_strong h hSE hz).symm
  unfold laplacian FLatticePaper.incomingNeg FLatticePaper.incomingPos
  simp only [hE, ↓reduceIte]
  norm_num
  rw [eMW _ m01, eMW _ m11, eMW _ m21]
  have F11 : standardField word (1, 1) = 0 := by
    apply hS.1
    · unfold ChildFrame.tGrade
      omega
    · unfold ChildFrame.tGrade
      omega
  have F21 : standardField word (2, 1) = 0 := by
    apply hS.1
    · unfold ChildFrame.tGrade
      omega
    · unfold ChildFrame.tGrade
      omega
  have F01 : standardField word (0, 1) = -1 := by
    rw [hS.2 (0, 1)]
    · exact harmonicGrid_zero_one
    · unfold ChildFrame.sGrade
      omega
    · unfold ChildFrame.sGrade
      omega
  rw [F11, F21, F01]
  norm_num

end FLatticePaper.Induction
