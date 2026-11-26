import FLatticePaper.Plane.Induction.SheetPieces
import FLatticePaper.Plane.Induction.OppWordCover
import FLatticePaper.Plane.Induction.W1MSheet
import FLatticePaper.Plane.Induction.StrongCoreDef
import FLatticePaper.Plane.Induction.W1Seeds
import FLatticePaper.Plane.Induction.StrongEstimates

/-! # The point `(1,1)` is never a white site of the sheet field `MW` (the input `hOne` of the row-face assembly)

On the closed polygon of the physical frame, `MW word` is the physical standard field (`standardField_eq_sheetMin_on_star`). The
star of `(1,1)` is `(0,1), (1,1), (2,1)`, all in the polygon. Its physical values are `F(0,1) = harmonicGrid (0,1) = -1` (the odd
band, `OppWordCover.word_odd_cover`), and `F(1,1) = F(2,1) = 0` (the zero strip). So `laplacian (MW word) (1,1) = -1`. -/

namespace FLatticePaper.ClassOne

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1MSheet FLatticePaper.OppWordCover

theorem one_ne (word : Farey.Word) (hw : ∃ x ∈ word, x ≠ Digit.three)
    (hSE : StrongEstimates (conjWord word)) (hcore : StrongCore word)
    (hseed : FLatticePaper.W1Seeds.SeedFields word) (c : Site)
    (hM : laplacian (MW word) c = 0) : c ≠ (1, 1) := by
  intro hc
  subst hc
  obtain ⟨hn0, hnd, hdn, hd3, hTd⟩ := (frameAt word).child_facts
  have hT := periodDenominator_pos (frameAt word)
  have hT2 : 2 * (frameAt word).child.den ≤ (frameAt word).child.periodDenominator := by
    rw [hTd]; nlinarith
  have hT3 : 3 * (frameAt word).child.den ≤ (frameAt word).child.periodDenominator + (frameAt word).child.num := by
    rw [hTd]; nlinarith
  have hpar := (frameAt word).child_odd
  -- the star of (1,1) lies in the closed polygon
  have hE1 : ((1 : ℤ), (1 : ℤ)) ∈ (frameAt word).closedPolygon := by
    refine ((frameAt word).mem_closedPolygon_iff _).mpr (Or.inl ⟨by decide, ?_, ?_, ?_, ?_⟩)
    · have : (frameAt word).tGrade (1, 1) = (frameAt word).child.num - (frameAt word).child.den := by
        unfold ChildFrame.tGrade; ring
      omega
    · have : (frameAt word).tGrade (1, 1) = (frameAt word).child.num - (frameAt word).child.den := by
        unfold ChildFrame.tGrade; ring
      omega
    · have : (frameAt word).sGrade (1, 1) = 2 * (frameAt word).child.den := by
        unfold ChildFrame.sGrade; ring
      omega
    · have : (frameAt word).sGrade (1, 1) = 2 * (frameAt word).child.den := by
        unfold ChildFrame.sGrade; ring
      omega
  have hE0 : ((0 : ℤ), (1 : ℤ)) ∈ (frameAt word).closedPolygon := by
    refine ((frameAt word).mem_closedPolygon_iff _).mpr (Or.inr ⟨by decide, ?_, ?_, ?_, ?_⟩)
    · have : (frameAt word).tGrade (0, 1) = -(frameAt word).child.den := by
        unfold ChildFrame.tGrade; ring
      omega
    · have : (frameAt word).tGrade (0, 1) = -(frameAt word).child.den := by
        unfold ChildFrame.tGrade; ring
      omega
    · have : (frameAt word).sGrade (0, 1) = (frameAt word).child.den - (frameAt word).child.num := by
        unfold ChildFrame.sGrade; ring
      omega
    · have : (frameAt word).sGrade (0, 1) = (frameAt word).child.den - (frameAt word).child.num := by
        unfold ChildFrame.sGrade; ring
      omega
  have hE2 : ((2 : ℤ), (1 : ℤ)) ∈ (frameAt word).closedPolygon := by
    refine ((frameAt word).mem_closedPolygon_iff _).mpr (Or.inr ⟨by decide, ?_, ?_, ?_, ?_⟩)
    · have : (frameAt word).tGrade (2, 1) = 2 * (frameAt word).child.num - (frameAt word).child.den := by
        unfold ChildFrame.tGrade; ring
      omega
    · have : (frameAt word).tGrade (2, 1) = 2 * (frameAt word).child.num - (frameAt word).child.den := by
        unfold ChildFrame.tGrade; ring
      omega
    · have : (frameAt word).sGrade (2, 1) = 3 * (frameAt word).child.den + (frameAt word).child.num := by
        unfold ChildFrame.sGrade; ring
      omega
    · have : (frameAt word).sGrade (2, 1) = 3 * (frameAt word).child.den + (frameAt word).child.num := by
        unfold ChildFrame.sGrade; ring
      omega
  -- the field equals the sheet minimum on the star
  have hq := standardField_eq_sheetMin_on_star hw hSE hE1 hE0 hE2
  obtain ⟨hv1, hv0, hv2⟩ := hq
  -- the physical values on the star
  have hstr := hcore.packet.strips
  have hF0 : standardField word (0, 1) = -1 := by
    have hh := word_odd_cover hcore hseed (0, 1) (by decide) (by omega)
      (by
        have : (frameAt word).sGrade (0, 1) = (frameAt word).child.den - (frameAt word).child.num := by
          unfold ChildFrame.sGrade; ring
        omega)
      (by
        have : (frameAt word).sGrade (0, 1) = (frameAt word).child.den - (frameAt word).child.num := by
          unfold ChildFrame.sGrade; ring
        omega)
    rw [hh]
    unfold harmonicGrid
    norm_num
  have hF1 : standardField word (1, 1) = 0 := by
    apply hstr.1
    · have : (frameAt word).tGrade (1, 1) = (frameAt word).child.num - (frameAt word).child.den := by
        unfold ChildFrame.tGrade; ring
      omega
    · have : (frameAt word).tGrade (1, 1) = (frameAt word).child.num - (frameAt word).child.den := by
        unfold ChildFrame.tGrade; ring
      omega
  have hF2 : standardField word (2, 1) = 0 := by
    apply hstr.1
    · have : (frameAt word).tGrade (2, 1) = 2 * (frameAt word).child.num - (frameAt word).child.den := by
        unfold ChildFrame.tGrade; ring
      omega
    · have : (frameAt word).tGrade (2, 1) = 2 * (frameAt word).child.num - (frameAt word).child.den := by
        unfold ChildFrame.tGrade; ring
      omega
  -- the Laplacian of MW at (1,1) equals that of the physical field, which is -1
  have hinNeg : incomingNeg ((1 : ℤ), (1 : ℤ)) = (0, 1) := by
    unfold incomingNeg; rw [if_pos (show EvenSite ((1 : ℤ), (1 : ℤ)) from by decide)]
    norm_num
  have hinPos : incomingPos ((1 : ℤ), (1 : ℤ)) = (2, 1) := by
    unfold incomingPos; rw [if_pos (show EvenSite ((1 : ℤ), (1 : ℤ)) from by decide)]
    norm_num
  have e1 : MW word ((1 : ℤ), (1 : ℤ)) = standardField word (1, 1) := hv1.symm
  have e0 : MW word ((0 : ℤ), (1 : ℤ)) = standardField word (0, 1) := hv0.symm
  have e2 : MW word ((2 : ℤ), (1 : ℤ)) = standardField word (2, 1) := hv2.symm
  unfold laplacian at hM
  rw [hinNeg, hinPos, e0, e1, e2, hF0, hF1, hF2] at hM
  norm_num at hM

end FLatticePaper.ClassOne
