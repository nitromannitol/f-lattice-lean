import FLatticePaper.Tiles.WeakStepAssembly
import FLatticePaper.Tiles.TileCompatInputs

/-! # The weak alternate step of the joint induction for the paper data

The weak alternate odometers of a word are glued from the pieces of their alternate decompositions. The two copies of a shifted
doubling of a register (shift `S_p` or `S_q`, `altShifts`, affine factor `a_{p,2}`) must agree on their overlap:
`AltShiftCompatInput` states it, at every word that is not a base word (`def:alternate_doubled_tile`: the two copies
respect the tile translations on their meeting string, and their overlap lies in that string, `lemma:alternate_tile_properties`).
The base cases (`BaseWeakAltInput`), (a) of `lemma:weak_alternate_odometer_properties` for the glued weak alternates at the
children that are not corrected (`AltGlueRespectsInput`), and the weak alternates at the corrected children
(`AltCorrectedWeakInput`) are stated as well, and the local compatibility of the alternate parent piece with the six standard
copies at the uncorrected alternate children (`AltPairCompatInput`). Stated, not proved here. -/

namespace FLatticePaper.Tiles.WeakAltStepAssembly

open FLatticePaper.Farey
open FLatticePaper.Construction (texV1Odd texV1Even texV2)
open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction (GoodBelow)
open FLatticePaper.Tiles.WeakStepPaper (paperS)
open FLatticePaper.Tiles.SurgicalWeak (regsAt)
open FLatticePaper.Tiles.Standard (IsBase)
open FLatticePaper.Tiles.SurgicalAlt (altRevVAnchor altFwdHAnchor RespectsHalfV RespectsHalfH AltOddNodeP AltEvenNodeP)
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.SurgicalAltTiles (altOddTile altEvenTile)

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

/-- **The base cases of the weak alternates** (`prop:base_cases`, the alternate base odometers): at a base word, weak alternate
odometers on the alternate tiles of the text with the alternate base condition, (a) of
`lemma:weak_alternate_odometer_properties` (the half strings at the anchors of the data) and its (b) along the second lattice
vector. -/
def BaseWeakAltInput (D : JointData) : Prop :=
  D.altBase = SurgicalAlt.PaperAltBaseCond → PaperAltAnc D → ∀ w : Word, IsBase w →
    ∃ wao wae : PartialOdometer, wao.dom = altOddTile PaperAltBase.paperAltBaseTiles w ∧
      wae.dom = altEvenTile PaperAltBase.paperAltBaseTiles w ∧ SurgicalAlt.PaperAltBaseCond w wao wae ∧
      RespectsHalfV (altRevVAnchor D.anc w) (vWordOf w false) wao.val ∧
      RespectsHalfH (altFwdHAnchor D.anc w) (hWordOf w true) wae.val ∧ WeakAltPropsU w wao wae

/-- **(a) of `lemma:weak_alternate_odometer_properties` for the glued weak alternates** at the alternate children that are not
corrected: an odometer on the alternate tile that respects the full alternate decomposition respects the half string of the
alternate child (the vertical one for the odd alternate child, the horizontal one for the even alternate child). -/
def AltGlueRespectsInput (D : JointData) : Prop :=
  D.S = paperS → D.altBase = SurgicalAlt.PaperAltBaseCond → PaperAltBdry D → PaperAltAnc D →
    D.lSides = paperLSides → ∀ (f : Word → JSlice) (w : Word) (o : PartialOdometer), GoodBelow D f w.length → ¬ IsBase w →
    (¬ CorrectedAfterTwo w → o.dom = altOddTile PaperAltBase.paperAltBaseTiles w →
      RespectsPieces o (tileAltOddPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (fun u => (below f w u).lOdd) w) →
      RespectsHalfV (altRevVAnchor D.anc w) (vWordOf w false) o.val) ∧
    (¬ CorrectedAfterThree w → o.dom = altEvenTile PaperAltBase.paperAltBaseTiles w →
      RespectsPieces o (tileAltEvenPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven)
        (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven) (fun u => (below f w u).lEven) w) →
      RespectsHalfH (altFwdHAnchor D.anc w) (hWordOf w true) o.val)

/-- **The weak alternates at the corrected alternate children** (the odd alternate child of a word ending in `2`, the even one of
a word ending in `3`; Step 1 of the proof of `lemma:weak_alternate_odometer_properties`, glued on the kept parts of the six
standard copies, with (a)): an odometer on the alternate tile with the alternate node and the half string. -/
def AltCorrectedWeakInput (D : JointData) : Prop :=
  D.S = paperS → D.altBase = SurgicalAlt.PaperAltBaseCond → PaperAltBdry D → PaperAltAnc D →
    D.lSides = paperLSides → ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length →
    (CorrectedAfterTwo w → ∃ wao : PartialOdometer, wao.dom = altOddTile PaperAltBase.paperAltBaseTiles w ∧
      AltOddNodeP D.S wao (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
        (fun u => (below f w u).aEven) w ∧
      RespectsHalfV (altRevVAnchor D.anc w) (vWordOf w false) wao.val) ∧
    (CorrectedAfterThree w → ∃ wae : PartialOdometer, wae.dom = altEvenTile PaperAltBase.paperAltBaseTiles w ∧
      AltEvenNodeP D.S wae (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
        (fun u => (below f w u).aEven) w ∧
      RespectsHalfH (altFwdHAnchor D.anc w) (hWordOf w true) wae.val)

/-- **The alternate parent piece and the six standard copies** (Case 3 of `lemma:tile-odometer-existence` for the alternate
decompositions): at an alternate child that is not corrected, the alternate parent piece (entry `6` of the full alternate
decomposition, when the type of the word keeps it) is locally compatible with each of the six standard copies. -/
def AltPairCompatInput (D : JointData) : Prop :=
  D.S = paperS → D.altBase = SurgicalAlt.PaperAltBaseCond → ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length →
    ¬ IsBase w →
    (¬ CorrectedAfterTwo w → ∀ j < 6, TileCompatInputs.PairCompat (tileAltOddPieces D.S (fun u => (below f w u).tOdd)
      (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven)
      (fun u => (below f w u).lOdd) w) 6 j) ∧
    (¬ CorrectedAfterThree w → ∀ j < 6, TileCompatInputs.PairCompat (tileAltEvenPieces D.S (fun u => (below f w u).tOdd)
      (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd) (fun u => (below f w u).aEven)
      (fun u => (below f w u).lEven) w) 6 j)

end FLatticePaper.Tiles.WeakAltStepAssembly
