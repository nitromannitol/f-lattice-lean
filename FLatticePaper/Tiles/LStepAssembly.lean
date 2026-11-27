import FLatticePaper.Tiles.JointInduction
import FLatticePaper.Tiles.JointGlue

/-! # The L step of the joint induction

`lStep_of_inputs` proves `JointInduction.LStepInput D`. The L-corrected odometer is the glue of the pieces of its decomposition
(`oddLPieces`, `evenLPieces`) with the constants of `lemma:l_correct_existence`. It respects the decomposition by
`respectsPieces_glued`; every point lies in a piece where it is not exceptional (`oddLPieces_covered`, `evenLPieces_covered`).

There are two named inputs:
* `LPiecesAgreeInput`, the constants with which the pieces agree. This is the compatibility part of the lemma: local
  compatibility of the pieces and the zero sum of the offsets around every closed path.
* `LSidesInput`, the agreement of the glued odometer with the child on the sides (`lemma:l_correc_properties` (2)). -/

namespace FLatticePaper.Tiles.LStepAssembly

open FLatticePaper.Farey
open FLatticePaper.Tiles
open FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.JointInduction
open FLatticePaper.Tiles.JointGlue
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)

/-- The pieces of the odd L-corrections of `w`, over the family below `w`. -/
abbrev oddPs (D : JointData) (f : Word → JSlice) (w : Word) (plus elong : Bool) : List Piece :=
  oddLPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
    (fun u => (below f w u).aEven) w plus elong

/-- The pieces of the even L-corrections of `w`, over the family below `w`. -/
abbrev evenPs (D : JointData) (f : Word → JSlice) (w : Word) (plus elong : Bool) : List Piece :=
  evenLPieces D.S (fun u => (below f w u).tOdd) (fun u => (below f w u).tEven) (fun u => (below f w u).aOdd)
    (fun u => (below f w u).aEven) w plus elong

/-- The compatibility part of `lemma:l_correct_existence`: the pieces of each L-correction agree, outside their exceptional
points, after adding one constant per piece. -/
def LPiecesAgreeInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word), GoodBelow D f w.length → ∀ plus elong : Bool,
    (OddLDefined w → ∃ κ : ℕ → ℤ, PiecesAgree (oddPs D f w plus elong) κ) ∧
      (EvenLDefined w → ∃ κ : ℕ → ℤ, PiecesAgree (evenPs D f w plus elong) κ)

/-- The sides part of `lemma:l_correct_existence` (`lemma:l_correc_properties` (2)): with any constants with which the pieces
agree, the glued L-corrected odometer agrees with the tile odometer of the child on the sides `D.lSides`, up to a constant. -/
def LSidesInput (D : JointData) : Prop :=
  ∀ (f : Word → JSlice) (w : Word) (wo we wao wae tod tev aod aev : PartialOdometer), GoodBelow D f w.length →
    WeakPart D (below f w) w wo we → WeakAltPart D (below f w) w wao wae →
    TilePart D (below f w) w wo we wao wae tod tev aod aev → TileProps w tod tev aod aev →
    ∀ (plus elong : Bool) (κ : ℕ → ℤ),
      (OddLDefined w → PiecesAgree (oddPs D f w plus elong) κ →
        LSidesAgree (gluedOdo (oddPs D f w plus elong) κ) tod (hWordOf w false) (vWordOf w false)
          (D.lSides true (W1Odd w) plus elong)) ∧
      (EvenLDefined w → PiecesAgree (evenPs D f w plus elong) κ →
        LSidesAgree (gluedOdo (evenPs D f w plus elong) κ) tev (hWordOf w true) (vWordOf w true)
          (D.lSides false (W1Odd w) plus elong))

open Classical in
/-- **The L step**: `LStepInput D` from the compatibility and the sides of the L-corrections. -/
theorem lStep_of_inputs (D : JointData) (hag : LPiecesAgreeInput D) (hsd : LSidesInput D) : LStepInput D := by
  intro f w wo we wao wae tod tev aod aev hgood hW hWA hT hTP
  refine ⟨fun plus elong => if h : OddLDefined w then
      gluedOdo (oddPs D f w plus elong) (Classical.choose ((hag f w hgood plus elong).1 h)) else ⟨∅, fun _ => 0⟩,
    fun plus elong => if h : EvenLDefined w then
      gluedOdo (evenPs D f w plus elong) (Classical.choose ((hag f w hgood plus elong).2 h)) else ⟨∅, fun _ => 0⟩,
    fun plus elong hd => ?_, fun plus elong hd => ?_⟩
  · have hκ := Classical.choose_spec ((hag f w hgood plus elong).1 hd)
    simp only [dif_pos hd]
    exact ⟨respectsPieces_glued _ _ (oddLPieces_covered _ _ _ _ _ w plus elong) hκ,
      (hsd f w wo we wao wae tod tev aod aev hgood hW hWA hT hTP plus elong _).1 hd hκ⟩
  · have hκ := Classical.choose_spec ((hag f w hgood plus elong).2 hd)
    simp only [dif_pos hd]
    exact ⟨respectsPieces_glued _ _ (evenLPieces_covered _ _ _ _ _ w plus elong) hκ,
      (hsd f w wo we wao wae tod tev aod aev hgood hW hWA hT hTP plus elong _).2 hd hκ⟩

end FLatticePaper.Tiles.LStepAssembly
