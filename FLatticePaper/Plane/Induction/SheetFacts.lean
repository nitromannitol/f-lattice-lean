import FLatticePaper.Plane.Induction.StandardField
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.SheetSwap
import FLatticePaper.Plane.Induction.SheetRegions

namespace FLatticePaper.Induction
open Farey

/-- The odd register of a proper word has positive numerator: it is `N + nq` for the odd register `N/D` and the
even register `nq/dq` of the birth prefix, and the even register has numerator at least one. -/
theorem frameAt_odd_num_pos {word : Word} (h : ∃ x ∈ word, x ≠ .three) :
    0 < (frameAt word).parents.odd.num := by
  show 0 < (parentsAt word).odd.num
  rw [parentsAt_odd_eq h]
  obtain ⟨hden, hnum0, -⟩ := (parentsAt_valid (oddBirthPrefix word)).even_bounds
  obtain ⟨-, hodd0, -⟩ := (parentsAt_valid (oddBirthPrefix word)).odd_bounds
  have hevenpos : 1 ≤ (parentsAt (oddBirthPrefix word)).even.num := by
    by_contra hcon
    have h0 : (parentsAt (oddBirthPrefix word)).even.num = 0 := by omega
    have hred := (parentsAt_valid (oddBirthPrefix word)).even_reduced
    unfold Fraction.Reduced at hred
    rw [h0, isCoprime_zero_left, Int.isUnit_iff] at hred
    have hpar := (parentsAt_valid (oddBirthPrefix word)).even_parity
    unfold Fraction.Even at hpar
    rw [h0] at hpar
    omega
  show 0 < 1 * (parentsAt (oddBirthPrefix word)).odd.num + 1 * (parentsAt (oddBirthPrefix word)).even.num
  omega

/-- The sheet facts that follow from the conjugate packet. -/
theorem sheetFacts_of_conjPacket {word : Word} (h : ∃ x ∈ word, x ≠ .three) {G : Field}
    (hG : (frameAt ((oddBirthPrefix word).map Digit.swapTwoThree)).Packet G) :
    let frame := frameAt word
    let Fp := quarterTurnField G
    (∀ z ∈ frame.closedPolygon, 1 - frame.child.den ≤ frame.tGrade z → frame.sheetA Fp z = 0) ∧
    (∀ z ∈ frame.closedPolygon, frame.sGrade z ≤ 2 * (frame.child.den + frame.child.num) - 1 →
      (if frame.eps = 1 then frame.sheetA Fp z else frame.sheetC Fp z) = harmonicGrid z) ∧
    (∀ z, frame.sheetMin Fp (frame.centre - z) = frame.sheetMin Fp z - frame.tGrade z + frame.symmetryConstant) ∧
    (∀ z, (laplacian (frame.sheetA Fp) z = -1 ∨ laplacian (frame.sheetA Fp) z = 0) ∧
      (laplacian (frame.sheetC Fp) z = -1 ∨ laplacian (frame.sheetC Fp) z = 0)) := by
  intro frame Fp
  have hconj := frameAt_conj_child h
  have hN := frameAt_odd_num_pos h
  refine ⟨fun z hz ht => ?_, fun z hz hs => ?_, fun z => ?_, fun z => ?_⟩
  · exact frame.sheetA_eq_zero (frameAt ((oddBirthPrefix word).map Digit.swapTwoThree)) hconj hG.strips hz ht
  · exact frame.sheet_eq_harmonic (frameAt ((oddBirthPrefix word).map Digit.swapTwoThree)) hconj hG.strips hz hs hN
  · exact frame.sheetMin_reflection (frameAt ((oddBirthPrefix word).map Digit.swapTwoThree)) hconj
      hG.reflection hG.periods z
  · exact frame.sheets_binary hG.binary z

end FLatticePaper.Induction
