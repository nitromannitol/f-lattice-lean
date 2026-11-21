import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.StandardField
import FLatticePaper.Plane.Induction.Strips
import FLatticePaper.Plane.Induction.Reflection
import FLatticePaper.Plane.Induction.Binary

namespace FLatticePaper.Induction
open Farey

/-! The induction step for the packet: the sheet minimum of a proper word, with the sheet facts, is a field with
the full packet. -/

/-- The sheet minimum has the strip inputs, from the sheet facts on `E`. -/
theorem ChildFrame.stripInputs_sheetMin (frame : ChildFrame) {Fp : Field}
    (hA0 : ∀ z ∈ frame.closedPolygon, 1 - frame.child.den ≤ frame.tGrade z → frame.sheetA Fp z = 0)
    (hC0 : ∀ z ∈ frame.closedPolygon, 1 - frame.child.den ≤ frame.tGrade z → 0 ≤ frame.sheetC Fp z)
    (hEq : ∀ z ∈ frame.closedPolygon, frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1 →
      (if frame.eps = 1 then frame.sheetA Fp z else frame.sheetC Fp z) = harmonicGrid z)
    (hGe : ∀ z ∈ frame.closedPolygon, frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1 →
      harmonicGrid z ≤ (if frame.eps = 1 then frame.sheetC Fp z else frame.sheetA Fp z))
    (hrefl : ∀ z, frame.sheetMin Fp (frame.centre - z) =
      frame.sheetMin Fp z - frame.tGrade z + frame.symmetryConstant) :
    frame.StripInputs (frame.sheetMin Fp) where
  zero := fun z hz ht => by
    unfold ChildFrame.sheetMin
    rw [hA0 z hz ht]
    exact min_eq_left (hC0 z hz ht)
  harmonic := fun z hz hs => by
    by_cases heps : frame.eps = 1
    · simp only [if_pos heps] at hEq hGe
      unfold ChildFrame.sheetMin
      rw [hEq z hz hs]
      exact min_eq_left (hGe z hz hs)
    · simp only [if_neg heps] at hEq hGe
      unfold ChildFrame.sheetMin
      rw [hEq z hz hs]
      exact min_eq_right (hGe z hz hs)
  reflection := fun z _ => hrefl z

/-- The induction step for the packet: the sewn standard of the sheet minimum has the full packet. -/
theorem ChildFrame.packet_of_sheets (frame : ChildFrame) {Fp : Field}
    (hA0 : ∀ z ∈ frame.closedPolygon, 1 - frame.child.den ≤ frame.tGrade z → frame.sheetA Fp z = 0)
    (hC0 : ∀ z ∈ frame.closedPolygon, 1 - frame.child.den ≤ frame.tGrade z → 0 ≤ frame.sheetC Fp z)
    (hEq : ∀ z ∈ frame.closedPolygon, frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1 →
      (if frame.eps = 1 then frame.sheetA Fp z else frame.sheetC Fp z) = harmonicGrid z)
    (hGe : ∀ z ∈ frame.closedPolygon, frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1 →
      harmonicGrid z ≤ (if frame.eps = 1 then frame.sheetC Fp z else frame.sheetA Fp z))
    (hrefl : ∀ z, frame.sheetMin Fp (frame.centre - z) =
      frame.sheetMin Fp z - frame.tGrade z + frame.symmetryConstant)
    (hbin : ∀ z ∈ frame.closedPolygon, laplacian (frame.sheetMin Fp) z = -1 ∨
      laplacian (frame.sheetMin Fp) z = 0) :
    frame.Packet (frame.sewnField (frame.sheetMin Fp) frame.coherentConstantU frame.coherentConstantV) := by
  have hS := frame.stripInputs_sheetMin hA0 hC0 hEq hGe hrefl
  have hH := hS.heightInputs
  obtain ⟨hagree, hper⟩ := frame.sewnField_spec (frame.respectsPeriodsOn_of_heightInputs hH)
  have hstrips := frame.hasStrips_of_stripInputs hS hagree hper
  have hreflF := frame.reflection_of_heightInputs hH hagree hper
  have hbinF := frame.binary_of_strips hper hagree hbin hstrips hreflF
  exact ⟨hper, hstrips, hreflF, hbinF⟩

end FLatticePaper.Induction
