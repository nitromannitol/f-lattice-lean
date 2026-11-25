import FLatticePaper.Plane.Induction.CollarChain

/-! # The face of a collar centre, the sign of `Ψ` per face, and the face-restricted row input

A strict collar centre `c` lies on one of four faces of the child rectangle, read off from its collar witnesses (`CollarFrame`):

* bottom: a free H point at Chebyshev distance `≤ 1` (the disjunct `v ∈ freeH`);
* top: a free H point translated by the transverse vector (`v − transverse ∈ freeH`);
* left vertical: a free V point (`v ∈ freeV`);
* right vertical: a free V point translated by the kernel (`v − kernel ∈ freeV`).

The aligned vertical face is the left one when `ε = 1` (`W = 1`) and the right one when `ε = −1` (`W = 0`); the opposite vertical face is the other.

The numerical sign check (words of length at most 5, 358 words, the sheet field `Ψ = C − A` at every white strict collar centre) gives
`Ψ ≥ 0` on the bottom and on the aligned face, `Ψ ≤ 0` on the top and on the opposite face, with zeros only in reflected pairs.
`PsiFaceSign` is this statement (a named premise, not yet proved). `RowFaceStrictHyp` is `RowStrictHyp` restricted to centres on the
bottom or the aligned face. -/

namespace FLatticePaper.FaceSign

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.SquareClauses FLatticePaper.AndOrRank
open FLatticePaper.W1NonfreeOut FLatticePaper.CollarSquare FLatticePaper.W1SheetSquare FLatticePaper.W1PrivateSquare
open FLatticePaper.W1NonfreeHsqNonneg FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.W1CollarFrame
open FLatticePaper.W1NonfreeHsqC FLatticePaper.ChainWire FLatticePaper.CollarChain

/-- The bottom face: a free H point within one pixel. -/
def BottomWit (frame : ChildFrame) (c : Site) : Prop :=
  ∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ v ∈ frame.freeH

/-- The top face: a free H point translated by the transverse vector, within one pixel. -/
def TopWit (frame : ChildFrame) (c : Site) : Prop :=
  ∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ (v - frame.child.modifiedDeck.transverse) ∈ frame.freeH

/-- The left vertical face: a free V point within one pixel. -/
def LeftWit (frame : ChildFrame) (c : Site) : Prop :=
  ∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ v ∈ frame.freeV

/-- The right vertical face: a free V point translated by the kernel, within one pixel. -/
def RightWit (frame : ChildFrame) (c : Site) : Prop :=
  ∃ v : Site, |v.1 - c.1| ≤ 1 ∧ |v.2 - c.2| ≤ 1 ∧ (v - frame.child.modifiedDeck.kernel) ∈ frame.freeV

/-- The aligned vertical face: left when `ε = 1` (`W = 1`), right when `ε = −1` (`W = 0`). -/
def AlignedWit (frame : ChildFrame) (c : Site) : Prop :=
  (frame.eps = 1 ∧ LeftWit frame c) ∨ (frame.eps = -1 ∧ RightWit frame c)

/-- The opposite vertical face: right when `ε = 1`, left when `ε = −1`. -/
def OppositeWit (frame : ChildFrame) (c : Site) : Prop :=
  (frame.eps = 1 ∧ RightWit frame c) ∨ (frame.eps = -1 ∧ LeftWit frame c)

/-- **The sign of `Ψ` per face** (named premise; numerically checked on 358 words of length at most 5). For a white strict collar
centre, `Ψ ≥ 0` on the bottom or the aligned face, and `Ψ ≤ 0` on the top or the opposite face. -/
def PsiFaceSign (word : Word) : Prop :=
  ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
    laplacian (MW word) c = 0 → CollarFrame (frameAt word) c →
    ((BottomWit (frameAt word) c ∨ AlignedWit (frameAt word) c) → 0 ≤ sheetPsi word c) ∧
    ((TopWit (frameAt word) c ∨ OppositeWit (frameAt word) c) → sheetPsi word c ≤ 0)

/-- **`RowStrictHyp` restricted to the bottom or aligned face**: the explicit parent square with strictly interior child corners, at a
strict collar centre with `Ψ ≥ 0` on the bottom or the aligned face whose parent root is free. -/
def RowFaceStrictHyp (word : Word) (G : Field) (R : Site → Site → Prop) : Prop :=
  ∀ c : Site, FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den c →
    laplacian (MW word) c = 0 → 0 ≤ sheetPsi word c → CollarFrame (frameAt word) c →
    (BottomWit (frameAt word) c ∨ AlignedWit (frameAt word) c) →
    ¬ Nonfree (frameAt (conjWord word)) (zTurn (c - (frameAt word).sheetShift)) →
    ∃ q0 q1 q2 o : Site, ∃ qa qb : ℤ,
      PSquare G R (zTurn (c - (frameAt word).sheetShift)) q0 q1 q2 o qa qb ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + FLatticePaper.W1Phase.zTurnInv q0) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + FLatticePaper.W1Phase.zTurnInv q1) ∧
      FLatticePaper.W1.StrictInterior (frameAt word).child.num (frameAt word).child.den
        ((frameAt word).sheetShift + FLatticePaper.W1Phase.zTurnInv q2)

end FLatticePaper.FaceSign
