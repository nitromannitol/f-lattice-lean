import FLatticePaper.Tiles.SurgicalWeakOdometers
import FLatticePaper.Tiles.LCorrections
import FLatticePaper.Tiles.SurgicalAltTiles

/-! # The joint weak/tile odometer family (Sections 7-8)

Design: `tasks/joint-family.md` (lead). The parents of every node are the TILE odometers of the parent words (Section 8,
`274ad18`), so the weak family and the tile family form one induction over the word. This module states the tile step (2)
and the joint predicate (1)-(3). The parent-parameterised node predicates (`OddN`, `EvenN`, w3's Section 7 work) are arguments,
so they plug in unchanged. The L-corrected tile domains of corrected children are the cell sets of `LCorrections`, translated
by the initial offset of the copy they replace (`evenChildB`, validated on word 2).

Open readings, kept as parameters and flagged for the operator: the initial offset for the odd child and for `W_1` odd, the
elongation used for the tile odometer (`elongated = true` below), and the alternate base (`altBase`, `prop:base_cases`). -/

namespace FLatticePaper.Tiles.JointFamily

open FLatticePaper.Farey
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.Standard (IsBase stateAt)

/-- The odd L-correction condition on the child `T(p_0)` of `w`: `w = w_1 s 2^k` with `s ≠ 2` (`def:odd_l_correction`). -/
def OddCorrected (w : Word) : Prop :=
  ∃ (w1 : Word) (s : Digit) (k : ℕ), s ≠ Digit.two ∧ w = w1 ++ [s] ++ List.replicate k Digit.two

/-- The even L-correction condition on the child `T(q_0)` of `w`: `w = w_1 s 3^k` with `s ≠ 3` (`def:even_l_correction`). -/
def EvenCorrected (w : Word) : Prop :=
  ∃ (w1 : Word) (s : Digit) (k : ℕ), s ≠ Digit.three ∧ w = w1 ++ [s] ++ List.replicate k Digit.three

/-- The number of trailing copies of the digit `d` in `w`. -/
def trailingCount (d : Digit) (w : Word) : ℕ :=
  (w.reverse.takeWhile (fun x => decide (x = d))).length

/-- The word with its trailing copies of `d` removed. -/
def stripTrailing (d : Digit) (w : Word) : Word :=
  w.take (w.length - trailingCount d w)

/-- The L-corrected domain of the even child `T(q_0)` of `w = w_1 s 3^k`, elongated, with the alternate base `altBase`,
translated by the initial offset `off w plus` (the copy the correction replaces, `evenChildB`). -/
def evenCell (altBase : Word → Standard.Tile × Standard.Tile) (off : Word → Bool → Site) (w : Word) (plus : Bool) :
    Finset Site :=
  let pre := stripTrailing Digit.three w
  let k := trailingCount Digit.three w
  let odd := phase pre == 1
  let s2 := decide (pre.getLast? = some Digit.two)
  let dbl := !pre.isEmpty && pre.all (fun d => decide (d = Digit.two))
  let st := stateAt pre
  let pq := LCorrections.wordParents pre
  LCorrections.shiftCells
    (LCorrections.evenLCorrection k true dbl st.tOdd st.tEven
      (SurgicalAltTiles.altRegs altBase pre).1 (SiteStrings.baseSites Letter.q true).toFinset pq.1 pq.2 odd plus s2)
    (off w plus)

/-- The tile step (2) of the joint family: a child that is not corrected by Section 8 has the weak odometer as its tile odometer;
a corrected child has the L-corrected domain `corrDom w parity` (`true`: odd child). -/
def TileStep (corrDom : Word → Bool → Finset Site) (wOddO wEvenO tOddO tEvenO : Word → PartialOdometer) : Prop :=
  ∀ w : Word,
    (¬ OddCorrected w → tOddO w = wOddO w) ∧ (OddCorrected w → (tOddO w).dom = corrDom w true) ∧
    (¬ EvenCorrected w → tEvenO w = wEvenO w) ∧ (EvenCorrected w → (tEvenO w).dom = corrDom w false)

/-- The joint predicate: (1) the weak step over the tile parents (`OddN`, `EvenN`, with `S.base` on base words, the tile and
weak odometers coinciding there), (2) the tile step, (3) the respect conjuncts for the tile odometers. The node predicates
`OddN`, `EvenN` take the weak children and the tile parents, `OddN S wOddO wEvenO tOddO tEvenO w`. -/
def IsJointFamily (S : WeakData)
    (OddN EvenN : WeakData → (Word → PartialOdometer) → (Word → PartialOdometer) →
      (Word → PartialOdometer) → (Word → PartialOdometer) → Word → Prop)
    (corrDom : Word → Bool → Finset Site)
    (wOddO wEvenO tOddO tEvenO : Word → PartialOdometer) : Prop :=
  ∀ w : Word,
    (wOddO w).dom = S.bdry (some w) true ∧ (wEvenO w).dom = S.bdry (some w) false ∧
    (IsBase w → S.base w (wOddO w) (wEvenO w) ∧ tOddO w = wOddO w ∧ tEvenO w = wEvenO w) ∧
    (¬ IsBase w → OddN S wOddO wEvenO tOddO tEvenO w ∧ EvenN S wOddO wEvenO tOddO tEvenO w) ∧
    (¬ OddCorrected w → tOddO w = wOddO w) ∧ (OddCorrected w → (tOddO w).dom = corrDom w true) ∧
    (¬ EvenCorrected w → tEvenO w = wEvenO w) ∧ (EvenCorrected w → (tEvenO w).dom = corrDom w false) ∧
    RespectsAnchored (tOddO w).dom (SiteStrings.hWordOf w false) (SiteStrings.vWordOf w false) (tOddO w).val ∧
    RespectsAnchored (tEvenO w).dom (SiteStrings.hWordOf w true) (SiteStrings.vWordOf w true) (tEvenO w).val

end FLatticePaper.Tiles.JointFamily
