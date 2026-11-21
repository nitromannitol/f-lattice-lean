import FLatticePaper.Plane.Induction.WordInduction
import FLatticePaper.Plane.Induction.SheetRegions
import FLatticePaper.Plane.Induction.Packet
import FLatticePaper.Plane.Induction.SheetDifference

namespace FLatticePaper.Induction
open Farey

/-- The second open input (I2) from a two-sided bound on the earlier chain potential over the image of the harmonic
region `E ∩ {s ≤ 2L − 1}`. For `ε = 1` the sheet C is at least `h₀` because `C − A = Ψ = K − Φ' ≥ 0` there (A is
`h₀`); for `ε = −1` the sheet A is at least `h₀` because `A − C = Φ' − K ≥ 0` there (C is `h₀`). -/
theorem openInput_two_of_chainBound {word : Word} (h : ∃ x ∈ word, x ≠ Digit.three)
    (hG : (frameAt (conjWord word)).Packet (standardField (conjWord word)))
    {K : ℤ}
    (hK : ∀ z : Site,
      (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z -
        (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z +
        FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
          (frameAt (oddBirthPrefix word)).eps (frameAt word).eps
          (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1) = K)
    (hbound : ∀ z ∈ (frameAt word).closedPolygon,
      (frameAt word).sGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1 →
        ((frameAt word).eps = 1 →
          FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
            (frameAt (oddBirthPrefix word)).eps (frameAt word).eps
            (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1) ≤ K) ∧
        ((frameAt word).eps = -1 →
          K ≤ FLatticePaper.earlierChainPrice (standardField (conjWord word)) (frameAt (conjWord word)).parents.odd
            (frameAt (oddBirthPrefix word)).eps (frameAt word).eps
            (-(z - (frameAt word).sheetShift).2, (z - (frameAt word).sheetShift).1 - 1))) :
    ∀ z ∈ (frameAt word).closedPolygon,
      (frameAt word).sGrade z ≤ 2 * ((frameAt word).child.den + (frameAt word).child.num) - 1 →
        harmonicGrid z ≤
          (if (frameAt word).eps = 1 then (frameAt word).sheetC (quarterTurnField (standardField (conjWord word))) z
            else (frameAt word).sheetA (quarterTurnField (standardField (conjWord word))) z) := by
  intro z hz hs
  have hh := ChildFrame.sheet_eq_harmonic (frameAt word) (frameAt (conjWord word)) (frameAt_conj_child h)
    hG.strips hz hs (frameAt_odd_num_pos h)
  have hk := hK z
  have hb := hbound z hz hs
  by_cases heps : (frameAt word).eps = 1
  · rw [if_pos heps] at hh ⊢
    have hbp := hb.1 heps
    rw [hh] at hk
    linarith
  · have hm1 : (frameAt word).eps = -1 := by
      rcases (frameAt word).eps_unit with h1 | h1
      · exact absurd h1 heps
      · exact h1
    rw [if_neg heps] at hh ⊢
    have hbm := hb.2 hm1
    rw [hh] at hk
    linarith

end FLatticePaper.Induction
