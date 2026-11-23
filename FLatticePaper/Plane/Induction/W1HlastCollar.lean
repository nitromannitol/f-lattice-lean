import FLatticePaper.Plane.Induction.W1Phase

/-! # Task 74 (1): the collar square of `H_last`

The fixer's identification (Q15, "Endpoint squares in their actual charts"): in the parent's coordinates the root `H_last − U` is
`(0, −1)`, and its core square is the reflected upper-right `H`-origin square, the lower-left corner `(−1, −2)` of
`squareCorners (−1) (−2)`. Its three-edge return from the rejected corner `(0, −2)` runs
`(0, −2) → (−1, −2) → (−1, −1) → (0, −1)` (the minus route; the plus route gives the same square).

As for the other collar lemmas (`collar_Vlast_upperRight`), the parent's core claim, that every non-root corner of the square reaches the
root along retained parent edges, is a hypothesis. The lemma transports it through the sheet map (`sheet_private_square`): the child
root lies in the child square `squareCorners (lv.1 − 1) lv.2`, and every other corner reaches it along the A sheet policy. -/

namespace FLatticePaper.W1HlastCollar

open Farey FLatticePaper FLatticePaper.SquareClauses FLatticePaper.AndOrRank FLatticePaper.Induction FLatticePaper.W1
open FLatticePaper.W1Forcing FLatticePaper.W1Witness FLatticePaper.W1Phase

/-- **The collar square of `H_last`** (task 74 (1)): the core square `squareCorners (−1) (−2)` of the root `(0, −1)`, transported to
the child square `squareCorners (lv.1 − 1) lv.2` through the child root `c` over `(0, −1)`. -/
theorem collar_Hlast {frame : ChildFrame} {G : Field} {seed : Site → Site → Prop} (P : OldPolicyRanked frame G seed)
    (lv : Site) {c : Site} (hc : zTurn (c - lv) = (0, -1))
    (hchain : ∀ q ∈ squareCorners (-1) (-2), q ≠ (0, -1) →
      Relation.TransGen (fun x y => P.retained x y ∧ Edge y x) q (0, -1)) :
    c ∈ squareCorners (lv.1 - 1) lv.2 ∧
      ∀ c' ∈ squareCorners (lv.1 - 1) lv.2, c' ≠ c →
        Relation.TransGen (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData lv) c' c := by
  have h := sheet_private_square P lv (-1) (-2) (by simp [squareCorners]) hc hchain
  have e1 : (-2 + 1 + lv.1 : ℤ) = lv.1 - 1 := by ring
  have e2 : (-(-1 : ℤ) - 1 + lv.2 : ℤ) = lv.2 := by ring
  rw [e1, e2] at h
  exact h

end FLatticePaper.W1HlastCollar
