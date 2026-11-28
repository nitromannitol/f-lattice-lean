import FLatticePaper.Tiles.WeakStepAssembly

/-! # The weak alternate step of the joint induction for the paper data

The weak alternate odometers of a word are glued from the pieces of their alternate decompositions. The two copies of a shifted
doubling of a register (shift `S_p` or `S_q`, `altShifts`, affine factor `a_{p,2}`) must agree on their overlap:
`AltShiftCompatInput` states it, at every word that is not a base word (`def:alternate_doubled_tile`: the two copies
respect the tile translations on their meeting string, and their overlap lies in that string, `lemma:alternate_tile_properties`).
Stated, not proved here. -/

namespace FLatticePaper.Tiles.WeakAltStepAssembly

open FLatticePaper.Farey
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.WeakStepPaper (paperS)
open FLatticePaper.Tiles.SurgicalWeak (regsAt)
open FLatticePaper.Tiles.Standard (IsBase)

/-- **The shifted doublings of the alternate decompositions** (`def:alternate_doubled_tile`): at every word that is not a base
word, the odd register (doubled in the odd alternate child) and the even register (doubled in the even alternate child) are
compatible with their translates by the alternate shift `S_p`, resp. `S_q`, with affine factor `a_{p,2}`. -/
def AltShiftCompatInput (D : JointData) : Prop :=
  D.S = paperS → D.altBase = SurgicalAlt.PaperAltBaseCond → ∀ (f : Word → JSlice) (w u1 u2 : Word),
    GoodBelow D f w.length → ¬ IsBase w → regsAt w = (some u1, some u2) →
    LatticeSelfCompatible (f u1).tOdd
        (SurgicalDict.altShifts (phase w == 1) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)).1
        (offsetA (parentsAt w).odd.num (parentsAt w).odd.den true) ∧
      LatticeSelfCompatible (f u2).tEven
        (SurgicalDict.altShifts (phase w == 1) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)).2
        (offsetA (parentsAt w).odd.num (parentsAt w).odd.den true)

end FLatticePaper.Tiles.WeakAltStepAssembly
