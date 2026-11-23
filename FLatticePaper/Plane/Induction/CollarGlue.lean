import FLatticePaper.Plane.Induction.W1NonfreeHsqNonneg
import FLatticePaper.Plane.Induction.CollarSquares
import FLatticePaper.Plane.Induction.CollarOneOne

/-! Task 72 (hcollar, the glue to `HsqAt`).

The collar square of a strict collar centre `c` is fixed by the arc of `c` alone (`collarBase`): bottom arc → upper-left square
`squareCorners (c.1 − 1) c.2`; otherwise left arc → upper-right square `squareCorners c.1 c.2`; otherwise right arc → lower-left
square `squareCorners (c.1 − 1) (c.2 − 1)`. The square contains `c` (`CollarSquares`).

The remaining content of `HsqAt` at a collar centre is inherited parent data, stated as the fields of `CollarChains`: the
rejected pointer lies outside the square, the corners are black or forced white with the output in the square, and the phase chains.
The strictness of the corners is a named input `hstrict` (to be discharged from the free-root band and `laplacian_MW_one_one`). -/

namespace FLatticePaper.CollarGlue

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.AndOrRank
open FLatticePaper.W1 FLatticePaper.W1Phase FLatticePaper.W1MSheet FLatticePaper.W1Step FLatticePaper.W1CollarFrame
open FLatticePaper.W1NonfreeHsqNonneg

/-- The bottom arc of the collar: a free H point (or a V-translate of one) within one pixel. -/
def BottomArc (frame : ChildFrame) (z : Site) : Prop :=
  ∃ v : Site, |v.1 - z.1| ≤ 1 ∧ |v.2 - z.2| ≤ 1 ∧
    (v ∈ frame.freeH ∨ (v - frame.child.modifiedDeck.transverse) ∈ frame.freeH)

/-- The left arc of the collar: a free V point within one pixel. -/
def LeftArc (frame : ChildFrame) (z : Site) : Prop :=
  ∃ v : Site, |v.1 - z.1| ≤ 1 ∧ |v.2 - z.2| ≤ 1 ∧ v ∈ frame.freeV

/-- The right arc of the collar: a V-translate (by the kernel) of a free V point within one pixel. -/
def RightArc (frame : ChildFrame) (z : Site) : Prop :=
  ∃ v : Site, |v.1 - z.1| ≤ 1 ∧ |v.2 - z.2| ≤ 1 ∧ (v - frame.child.modifiedDeck.kernel) ∈ frame.freeV

open Classical in
/-- The base `(a, b)` of the collar square of `c`, by the arc of `c` (bottom, then left, then right). -/
noncomputable def collarBase (frame : ChildFrame) (c : Site) : ℤ × ℤ :=
  if BottomArc frame c then (c.1 - 1, c.2)
  else if LeftArc frame c then (c.1, c.2)
  else (c.1 - 1, c.2 - 1)

/-- The collar square of `c`. -/
noncomputable def collarSquare (frame : ChildFrame) (c : Site) : Finset Site :=
  squareCorners (collarBase frame c).1 (collarBase frame c).2

/-- The collar centre lies in its collar square. -/
theorem centre_mem_collarSquare (frame : ChildFrame) (c : Site) : c ∈ collarSquare frame c := by
  unfold collarSquare collarBase
  split_ifs
  · exact bottom_centre_mem c
  · exact vPlus_centre_mem c
  · exact vMinus_centre_mem c

/-- **The inherited collar return chains** (the parent's collar data, `W1_CONSTRUCTOR` §2–§5, stated as fields like
`OldPolicyWitness`): at a collar centre with laplacian `0`, the rejected pointer is outside the collar square, the other corners
are black or forced white with the output inside the square, and the phase chains reach the centre. -/
structure CollarChains (word : Word) {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed) : Prop where
  out : ∀ c, CollarFrame (frameAt word) c → laplacian (MW word) c = 0 →
    sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c ∉ collarSquare (frameAt word) c
  corners : ∀ c, CollarFrame (frameAt word) c → laplacian (MW word) c = 0 →
    ∀ c' ∈ collarSquare (frameAt word) c, c' ≠ c →
      laplacian (MW word) c' = -1 ∨
        (laplacian (MW word) c' = 0 ∧
          sheetOut P (frameAt word).sheetShift (frameAt word).centre (sheetPsi word) c' ∈
            collarSquare (frameAt word) c)
  phase : ∀ c, CollarFrame (frameAt word) c → laplacian (MW word) c = 0 →
    ∀ c' ∈ collarSquare (frameAt word) c, c' ≠ c → laplacian (MW word) c' = 0 →
      PhaseOK (sheetPsi word) c c' ∧
        Relation.TransGen
          (phasePolicy (sheetPsi word)
            (sheetPolicyA P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift)
            (sheetPolicyC P.toOldPolicyWitness.toOldPolicyData (frameAt word).sheetShift (frameAt word).centre) c)
          c' c

/-- **The glue: `hcollar` from the inherited chains and the strictness of the collar square.** -/
theorem hcollar_of_chains {word : Word} {seed : Site → Site → Prop}
    (P : OldPolicyRanked (frameAt (conjWord word)) (standardField (conjWord word)) seed)
    (chains : CollarChains word P)
    (hstrict : ∀ c, CollarFrame (frameAt word) c → laplacian (MW word) c = 0 →
      ∀ c' ∈ collarSquare (frameAt word) c,
        StrictInterior (frameAt word).child.num (frameAt word).child.den c') :
    ∀ c : Site, StrictInterior (frameAt word).child.num (frameAt word).child.den c →
      laplacian (MW word) c = 0 → CollarFrame (frameAt word) c → HsqAt word P c := by
  intro c _hcS hM hcol
  unfold HsqAt
  refine ⟨(collarBase (frameAt word) c).1, (collarBase (frameAt word) c).2, ?_, ?_, ?_, ?_, ?_⟩
  · exact centre_mem_collarSquare (frameAt word) c
  · exact hstrict c hcol hM
  · exact chains.out c hcol hM
  · intro c' hc' hne
    exact chains.corners c hcol hM c' hc' hne
  · intro c' hc' hne hM'
    exact chains.phase c hcol hM c' hc' hne hM'

end FLatticePaper.CollarGlue
