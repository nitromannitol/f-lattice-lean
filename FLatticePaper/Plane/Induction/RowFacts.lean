import FLatticePaper.Plane.Induction.PSquareCorners
import FLatticePaper.Plane.Induction.RowCorners

/-! # The face rows from their parent facts

A face row is a parent square at the root `r = zTurn (c - lv)` of a collar centre `c` (`lv` the sheet shift), and its corner images are
strict (`RowCorners`). The policy part of the row is the set of facts at the root and at the three non-root corners of the square
(`SquareFacts`): the root keeps only its outward input, and each other corner retains its in-square successor (and nothing else if white).
Given these facts the row is a `PSquare` at the root on the face square, with strict corner images, which is the conclusion of
`CollarChain.RowStrictHyp` at `c`. The facts are the policy content of the row; they are not proved here. -/

namespace FLatticePaper.RowFacts

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AndOrRank FLatticePaper.CollarSquare FLatticePaper.FaceWitness
  FLatticePaper.PSquareCorners FLatticePaper.PrivateSquare FLatticePaper.W1Phase

/-- The policy facts of a parent square `squareCorners a b` at the root `z`: the root keeps exactly its outward input `o`, and every other
corner keeps its in-square successor, and only it when white. -/
def SquareFacts (G : Field) (R : Site → Site → Prop) (z : Site) (a b : ℤ) : Prop :=
  ∃ o : Site, (o = incomingNeg z ∨ o = incomingPos z) ∧ o ∉ squareCorners a b ∧ R z o ∧ (∀ j, R z j → j = o) ∧
    z ∈ squareCorners a b ∧
    ∀ y ∈ squareCorners a b, y ≠ z →
      R y (nxtS a b y) ∧ (laplacian G y = -1 ∨ (laplacian G y = 0 ∧ ∀ j, R y j → j = nxtS a b y))

/-- The `RowStrictHyp` conclusion at a collar centre `c` from the facts at its root, on a square whose corner images are strict.
The strictness of the images is the hypothesis `himg` (the face square lemma of `RowCorners`). -/
theorem pSquare_of_rowFacts {G : Field} {R : Site → Site → Prop} {a b : ℤ} {z : Site}
    (hF : SquareFacts G R z a b) :
    ∃ q0 q1 q2 o : Site, PSquare G R z q0 q1 q2 o a b := by
  obtain ⟨o, ho, hout, hRo, huniq, hz, hcorner⟩ := hF
  obtain ⟨q0, q1, q2, hP⟩ := pSquare_of_corners hz ho hout hRo huniq hcorner
  exact ⟨q0, q1, q2, o, hP⟩

/-- **Bottom row.** The bottom face centre `c` with root `z = zTurn (c - lv)`: the root facts on the upper-right square
`squareCorners (z.1 - 1) (z.2 - 1)` give the `RowStrictHyp` conclusion at `c`. -/
theorem bottom_row_of_facts {word : Word} {G : Field} {R : Site → Site → Prop} {c : Site}
    (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c) (hne : c ≠ (1, 1))
    (hB : BottomWit (frameAt word) c)
    (hF : SquareFacts G R (zTurn (c - (frameAt word).sheetShift))
      ((zTurn (c - (frameAt word).sheetShift)).1 - 1) ((zTurn (c - (frameAt word).sheetShift)).2 - 1)) :
    ∃ q0 q1 q2 o : Site, ∃ qa qb : ℤ,
      PSquare G R (zTurn (c - (frameAt word).sheetShift)) q0 q1 q2 o qa qb ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q0) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q1) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q2) := by
  obtain ⟨q0, q1, q2, o, hP⟩ := pSquare_of_rowFacts hF
  refine ⟨q0, q1, q2, o, _, _, hP, ?_, ?_, ?_⟩
  · exact RowCorners.bottom_row_strict hcS hne hB (hP.2.1)
  · exact RowCorners.bottom_row_strict hcS hne hB (hP.2.2.1)
  · exact RowCorners.bottom_row_strict hcS hne hB (hP.2.2.2.1)

/-- **Left row.** A left face centre (not bottom, not top) with root `z`: the root facts on the lower-right square
`squareCorners (z.1 - 1) z.2` give the `RowStrictHyp` conclusion at `c`. -/
theorem left_row_of_facts {word : Word} {G : Field} {R : Site → Site → Prop} {c : Site}
    (hn3 : 3 ≤ (frameAt word).child.num)
    (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hB : ¬ BottomWit (frameAt word) c) (hT : ¬ TopWit (frameAt word) c) (hL : LeftWit (frameAt word) c)
    (hF : SquareFacts G R (zTurn (c - (frameAt word).sheetShift))
      ((zTurn (c - (frameAt word).sheetShift)).1 - 1) (zTurn (c - (frameAt word).sheetShift)).2) :
    ∃ q0 q1 q2 o : Site, ∃ qa qb : ℤ,
      PSquare G R (zTurn (c - (frameAt word).sheetShift)) q0 q1 q2 o qa qb ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q0) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q1) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q2) := by
  obtain ⟨q0, q1, q2, o, hP⟩ := pSquare_of_rowFacts hF
  refine ⟨q0, q1, q2, o, _, _, hP, ?_, ?_, ?_⟩
  · exact RowCorners.left_row_strict hn3 hcS hB hT hL hP.2.1
  · exact RowCorners.left_row_strict hn3 hcS hB hT hL hP.2.2.1
  · exact RowCorners.left_row_strict hn3 hcS hB hT hL hP.2.2.2.1

/-- **Right row.** A right face centre (not bottom, not top) with root `z`: the root facts on the upper-left square
`squareCorners z.1 (z.2 - 1)` give the `RowStrictHyp` conclusion at `c`. -/
theorem right_row_of_facts {word : Word} {G : Field} {R : Site → Site → Prop} {c : Site}
    (hn3 : 3 ≤ (frameAt word).child.num)
    (hcS : FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c)
    (hB : ¬ BottomWit (frameAt word) c) (hT : ¬ TopWit (frameAt word) c) (hR : RightWit (frameAt word) c)
    (hF : SquareFacts G R (zTurn (c - (frameAt word).sheetShift)) (zTurn (c - (frameAt word).sheetShift)).1
      ((zTurn (c - (frameAt word).sheetShift)).2 - 1)) :
    ∃ q0 q1 q2 o : Site, ∃ qa qb : ℤ,
      PSquare G R (zTurn (c - (frameAt word).sheetShift)) q0 q1 q2 o qa qb ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q0) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q1) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + zTurnInv q2) := by
  obtain ⟨q0, q1, q2, o, hP⟩ := pSquare_of_rowFacts hF
  refine ⟨q0, q1, q2, o, _, _, hP, ?_, ?_, ?_⟩
  · exact RowCorners.right_row_strict hn3 hcS hB hT hR hP.2.1
  · exact RowCorners.right_row_strict hn3 hcS hB hT hR hP.2.2.1
  · exact RowCorners.right_row_strict hn3 hcS hB hT hR hP.2.2.2.1

end FLatticePaper.RowFacts
