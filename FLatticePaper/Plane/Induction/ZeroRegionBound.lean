import FLatticePaper.Plane.Induction.WordInduction
import FLatticePaper.Plane.Induction.SheetRegions
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.SheetDifference

namespace FLatticePaper.Induction
open Farey

/-- The first open input (I1) from a bound on the earlier chain potential over the image of the zero region.
The identity `Ψ(z) + Φ'(Z(z − lv)) = K` is the sheet difference identification; the bound is `Φ' ≤ K` on the image
of `E ∩ {t ≥ 1 − d}`. Then `sheetA = 0` there, so `sheetC = K − Φ' ≥ 0`. -/
theorem openInput_one_of_chainBound {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    {K : ℤ}
    (hK : ∀ z : Site,
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z +
        FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
          (frameAt (oddBirthPrefix word)).eps (frameAt word).eps
          (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1) = K)
    (hbound : ∀ z ∈ (frameAt word).closedPolygon, 1 - (frameAt word).child.den ≤ (frameAt word).tGrade z →
      FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
          (frameAt (oddBirthPrefix word)).eps (frameAt word).eps
          (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1) ≤ K) :
    ∀ z ∈ (frameAt word).closedPolygon, 1 - (frameAt word).child.den ≤ (frameAt word).tGrade z →
      0 ≤ (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z := by
  intro z hz ht
  have hA := ChildFrame.sheetA_eq_zero (frameAt word) (frameAt (conjWord word)) (frameAt_conj_child h)
    hG.strips hz ht
  have hk := hK z
  have hb := hbound z hz ht
  rw [hA] at hk
  linarith

end FLatticePaper.Induction
