import FLatticePaper.Plane.Induction.W1Step
import FLatticePaper.Plane.Induction.W1MSheet
import FLatticePaper.Plane.Induction.W1CollarFrame
import FLatticePaper.Plane.Induction.StandardField

/-! # The face witnesses and the sign of `Ψ` per face (a lower module, imported by `CollarChain` and `FaceSign`)

The four witnesses of a collar centre (bottom, top, left, right; the aligned and opposite vertical faces are the two V-faces, by
`ε`) and the named premise `PsiFaceSign`, as definitions only. They are used by `TopStrictHyp` (the forced-case strictness) and by
the callers that discharge it, so they live below `CollarChain`. -/

namespace FLatticePaper.FaceWitness

open Farey FLatticePaper FLatticePaper.Induction FLatticePaper.W1Step FLatticePaper.W1MSheet FLatticePaper.W1CollarFrame

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

end FLatticePaper.FaceWitness
