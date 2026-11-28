import FLatticePaper.Tiles.SurgicalAltTiles
import FLatticePaper.Tiles.PaperAltBase
import FLatticePaper.Tiles.LCorrections
import FLatticePaper.Tiles.SurgicalPartial
import FLatticePaper.Construction.BaseCaseRecurrence
import FLatticePaper.Construction.NearOneBaseCases
import FLatticePaper.Construction.QuarterTurnCorrection

/-! # The joint weak/tile odometer family (Sections 7-8)

Surgical edition 274ad18. The parents of every node are the TILE odometers of the parent words (`def:weak_standard_odometers`
with the proof of `lemma:weak_standard_odometer_properties`, and the unlabelled definition of tile odometers in
`subsec:full_recursion`), so the weak family, the tile family and the L-corrected odometers form one induction over the word.

* When an L-correction is defined (`OddLDefined`, `EvenLDefined`: `def:odd_l_correction`, `def:even_l_correction`) is separate
  from when a child is corrected (`CorrectedAfterThree`, `CorrectedAfterTwo`, the definition of tile odometers): the odd
  standard child and the even alternate child of `w = w''3` use the even L-corrections of `q_1 = T(q_0)` at `w''`; the even
  standard child and the odd alternate child of `w = w''2` use the odd L-corrections of `p_1 = T(p_0)` at `w''`.
* A tile odometer is its decomposition (`RespectsPieces`): the six standard copies (and the alternate parent for an
  alternate child) placed at the offsets of the weak nodes, with the tile odometers of the parents; at a corrected child two
  copies of the doubled parent are the L-corrected odometers of that parent, placed where the copies were
  (`eq:corner_l_correction`). The corrected copies are those of the weak nodes (`OddNodeP`, `EvenNodeP`, `AltOddNodeP`,
  `AltEvenNodeP`, the copy of the partial tile and the sign of `partialT`). Standard children use the short L-correction,
  alternate children the elongated one.
* An L-corrected odometer (`lemma:l_correct_existence`) is its decomposition (`oddLPieces`, `evenLPieces`): the stems, the bridge
  (with the `3^j` shift, and the copy of `T^d_{1/1}` after a `2^j`) and the heads of `LCorrections`, placed in the frame of the
  child (initial offset: the outer copy of `def:odd_l_correction`, `def:even_l_correction`), with the tile odometers of the parents
  of `w_1 s` and the alternate tile odometer for the heads; the only exception is the first head at the two points of the set
  `A` of its base lemma inside the last stem (`lemma:basecase_3k_even_alt`, `lemma:basecase_2k_odd_alt`), and only when
  `w_1 s = 3^j` (resp. `2^j`). It agrees with the tile odometer of the child on the sides of `lemma:l_correc_properties` (2).

Affine factors of the placed pieces follow the operator's rule (`pairAffine`, `coeffAffine`); the offsets of the L pieces are
the K-tables of `LCorrections` as coefficient vectors (`oddKCoeff_spec`, `evenKCoeff_spec`). Readings, flagged: the shifted
bridge of the `3^j` rule and the copy of `T^d_{1/1}` carry the affine factor of the unshifted bridge; the sides of the short
and of the odd L-corrections are a field (`JointData.lSides`), the printed ones being `printedEvenSides` for the elongated even
correction; the alternates are normalised like the standard tiles (`o = o_{1/1}` on the first tile at the origin). -/

namespace FLatticePaper.Tiles.JointFamily

open FLatticePaper.Farey
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SurgicalDict
open FLatticePaper.Tiles.SurgicalWeak
open FLatticePaper.Tiles.SurgicalAlt
open FLatticePaper.Tiles.SiteStrings (hWordOf vWordOf)
open FLatticePaper.Tiles.Standard (IsBase swapW)

/-! ### When an L-correction is defined, and when a child is corrected -/

/-- The odd L-correction `T^{L,±}(p_0)` of the odd child of `w` is defined: `w = w_1 s 2^k` with `s ≠ 2`
(`def:odd_l_correction`). -/
def OddLDefined (w : Word) : Prop :=
  ∃ (w1 : Word) (s : Digit) (k : ℕ), s ≠ Digit.two ∧ w = w1 ++ [s] ++ List.replicate k Digit.two

/-- The even L-correction `T^{L,±}(q_0)` of the even child of `w` is defined: `w = w_1 s 3^k` with `s ≠ 3`
(`def:even_l_correction`). -/
def EvenLDefined (w : Word) : Prop :=
  ∃ (w1 : Word) (s : Digit) (k : ℕ), s ≠ Digit.three ∧ w = w1 ++ [s] ++ List.replicate k Digit.three

/-- The children of `w` corrected by the even L-corrections of the even parent `q_1` (the even child of `w.dropLast`): the odd
standard child and the even alternate child of a word `w = w''3` that is not a base word (definition of tile odometers). -/
def CorrectedAfterThree (w : Word) : Prop := ¬ IsBase w ∧ w.getLast? = some Digit.three

/-- The children of `w` corrected by the odd L-corrections of the odd parent `p_1` (the odd child of `w.dropLast`): the even
standard child and the odd alternate child of a word `w = w''2` that is not a base word. -/
def CorrectedAfterTwo (w : Word) : Prop := ¬ IsBase w ∧ w.getLast? = some Digit.two

/-- The number of trailing copies of the digit `d` in `w`. -/
def trailingCount (d : Digit) (w : Word) : ℕ :=
  (w.reverse.takeWhile (fun x => decide (x = d))).length

/-- The word with its trailing copies of `d` removed. -/
def stripTrailing (d : Digit) (w : Word) : Word :=
  w.take (w.length - trailingCount d w)

/-! ### Placed pieces and decompositions -/

/-- A piece of a decomposition: a partial odometer placed at `off` with affine factor `aff`; `exc` is the set of points where
the decomposed odometer need not agree with this piece (empty except for the first head of an L-correction at a base
ancestor). -/
structure Piece where
  odo : PartialOdometer
  off : Site
  aff : Site
  exc : Set Site := ∅

/-- A piece with no exceptional point. -/
def stdPiece (o : PartialOdometer) (off aff : Site) : Piece := { odo := o, off := off, aff := aff }

/-- The placed domain of a piece. -/
def Piece.placed (p : Piece) : Finset Site := p.odo.dom.image (· + p.off)

/-- The union of the placed domains. -/
def pieceUnion (ps : List Piece) : Finset Site := ps.foldr (fun p acc => p.placed ∪ acc) ∅

/-- `o` respects the decomposition `ps`: its domain is the union of the placed domains, and on each placed domain (outside the
exceptional points of the piece) it is the placed piece plus its affine factor and a constant. -/
def RespectsPieces (o : PartialOdometer) (ps : List Piece) : Prop :=
  o.dom = pieceUnion ps ∧
    ∀ p ∈ ps, ∃ b : ℤ, ∀ x ∈ p.placed, x ∉ p.exc → o.val x = p.odo.val (x - p.off) + dotS p.aff x + b

/-! ### The vectors of the parents of a word -/

/-- `W_1` is odd for `w`. -/
def W1Odd (w : Word) : Bool := phase w == 1

/-- `v_{p_1,1}` of the odd parent of `w`. -/
def vP1 (w : Word) : Site := texV1Odd (parentsAt w).odd
/-- `v_{p_1,2}`. -/
def vP2 (w : Word) : Site := texV2 (parentsAt w).odd
/-- `v_{q_1,1}` of the even parent of `w`. -/
def vQ1 (w : Word) : Site := texV1Even (parentsAt w).even
/-- `v_{q_1,2}`. -/
def vQ2 (w : Word) : Site := texV2 (parentsAt w).even
/-- `a_{p_1,2} = (n_{p_1}, -d_{p_1})`. -/
def aP2 (w : Word) : Site := offsetA (parentsAt w).odd.num (parentsAt w).odd.den true
/-- `a_{q_1,2}`. -/
def aQ2 (w : Word) : Site := offsetA (parentsAt w).even.num (parentsAt w).even.den true

/-- The offsets of the pieces of the odd child (`offsetP0`, the tables of `IsStdStepP0W1Odd/Even`). -/
def p0Off (w : Word) (x : P0Piece) : Site := offsetP0 (W1Odd w) (vP1 w) (vP2 w) (vQ1 w) (vQ2 w) x

/-- The affine factors of the pieces of the odd child (`IsStdStepP0W1Odd`, `IsStdStepP0W1Even`). -/
def p0Aff (w : Word) (x : P0Piece) : Site :=
  let np := (parentsAt w).odd.num
  let dp := (parentsAt w).odd.den
  let nq := (parentsAt w).even.num
  let dq := (parentsAt w).even.den
  if W1Odd w then
    match x with
    | .p1Plus => pairAffine nq dq 0 0
    | .p1Minus => pairAffine nq dq 2 1
    | .q1DPlus => pairAffine np dp 1 0
    | .q1DMinus => pairAffine np dp 0 1
  else
    match x with
    | .p1Plus => pairAffine nq dq 2 0
    | .p1Minus => pairAffine nq dq 0 1
    | .q1DPlus => pairAffine np dp 0 0
    | .q1DMinus => pairAffine np dp 1 1

/-- The offsets of the pieces of the even child (`offsetQ0`). -/
def q0Off (w : Word) (x : Q0Piece) : Site := offsetQ0 (W1Odd w) (vP1 w) (vP2 w) (vQ1 w) (vQ2 w) x

/-- The affine factors of the pieces of the even child (`IsStdStepQ0W1Odd`, `IsStdStepQ0W1Even`). -/
def q0Aff (w : Word) (x : Q0Piece) : Site :=
  let np := (parentsAt w).odd.num
  let dp := (parentsAt w).odd.den
  let nq := (parentsAt w).even.num
  let dq := (parentsAt w).even.den
  if W1Odd w then
    match x with
    | .p1DPlus => pairAffine np dp 0 0
    | .p1DMinus => pairAffine nq dq 1 1
    | .q1Plus => pairAffine np dp 1 0
    | .q1Minus => pairAffine np dp 0 2
  else
    match x with
    | .p1DPlus => pairAffine nq dq 1 0
    | .p1DMinus => pairAffine nq dq 0 1
    | .q1Plus => pairAffine np dp 0 0
    | .q1Minus => pairAffine np dp 1 2

/-- The offset of a coefficient vector with the parents of `w`. -/
def altOff (w : Word) (c : AltCoeff) : Site := coeffOff (vP1 w) (vP2 w) (vQ1 w) (vQ2 w) c

/-- The affine factor of a coefficient vector with the parents of `w`. -/
def altAff (w : Word) (c : AltCoeff) : Site :=
  coeffAffine (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den c

/-! ### The tile decompositions (definition of tile odometers, `subsec:full_recursion`) -/

/-- The decomposition of the odd standard tile odometer of `w`, from the parent tile odometers `pOdd`, `pEven` (registers of
`w`) and the even L-corrected odometers `lEven u plus elongated`. The doubled parent `q_1` gives two copies at the offset of
`d(o)_{q_1}^±` and that offset plus `v_{q_1,1}`; after a `3` the copy of the partial tile of `OddNodeP` (the first copy when
`W_1` is odd, the second when even, for `+`; the other copy for `-`) is the short L-corrected odometer `o^{L,±}_{q_1}`. -/
def tileOddPieces (S : WeakData) (pOdd pEven : Word → PartialOdometer)
    (lEven : Word → Bool → Bool → PartialOdometer) (w : Word) : List Piece :=
  let P := regOdo S pOdd pEven (regsAt w).1 true
  let Q := regOdo S pOdd pEven (regsAt w).2 false
  let corr : Bool := decide (w.getLast? = some Digit.three)
  let o := W1Odd w
  let Lp := lEven w.dropLast true false
  let Lm := lEven w.dropLast false false
  [stdPiece P (p0Off w .p1Plus) (p0Aff w .p1Plus),
    stdPiece P (p0Off w .p1Minus) (p0Aff w .p1Minus),
    stdPiece (if corr && o then Lp else Q) (p0Off w .q1DPlus) (p0Aff w .q1DPlus),
    stdPiece (if corr && !o then Lp else Q) (p0Off w .q1DPlus + vQ1 w) (p0Aff w .q1DPlus),
    stdPiece (if corr && !o then Lm else Q) (p0Off w .q1DMinus) (p0Aff w .q1DMinus),
    stdPiece (if corr && o then Lm else Q) (p0Off w .q1DMinus + vQ1 w) (p0Aff w .q1DMinus)]

/-- The decomposition of the even standard tile odometer of `w`. The doubled parent `p_1` gives two copies at the offset of
`d(o)_{p_1}^±` and that offset plus `v_{p_1,2}` (affine factor plus `a_{p_1,2}`); after a `2` the second copy of `+` is
`o^{L,-}_{p_1}` and the first copy of `-` is `o^{L,+}_{p_1}` (the partial tiles of `EvenNodeP`), short. -/
def tileEvenPieces (S : WeakData) (pOdd pEven : Word → PartialOdometer)
    (lOdd : Word → Bool → Bool → PartialOdometer) (w : Word) : List Piece :=
  let P := regOdo S pOdd pEven (regsAt w).1 true
  let Q := regOdo S pOdd pEven (regsAt w).2 false
  let corr : Bool := decide (w.getLast? = some Digit.two)
  let Lp := lOdd w.dropLast true false
  let Lm := lOdd w.dropLast false false
  [stdPiece P (q0Off w .p1DPlus) (q0Aff w .p1DPlus),
    stdPiece (if corr then Lm else P) (q0Off w .p1DPlus + vP2 w) (q0Aff w .p1DPlus + aP2 w),
    stdPiece (if corr then Lp else P) (q0Off w .p1DMinus) (q0Aff w .p1DMinus),
    stdPiece P (q0Off w .p1DMinus + vP2 w) (q0Aff w .p1DMinus + aP2 w),
    stdPiece Q (q0Off w .q1Plus) (q0Aff w .q1Plus),
    stdPiece Q (q0Off w .q1Minus) (q0Aff w .q1Minus)]

/-- The decomposition of the odd alternate tile odometer of `w` (`eq:alt_odometer_decomposition`, first line): two copies of
the odd register for each shifted doubling (shift `S_p`, affine factor plus `a_{p_1,2}`), the even register twice, and the
alternate parent `ô(q_1)` when the type of `w` keeps it. After a `2` the second copy of `+` is `o^{L,-}_{p_1}` and the first copy
of `-` is `o^{L,+}_{p_1}` (the partial tiles of `AltOddNodeP`), elongated. -/
def tileAltOddPieces (S : WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lOdd : Word → Bool → Bool → PartialOdometer) (w : Word) : List Piece :=
  let P := regOdo S pOdd pEven (regsAt w).1 true
  let Q := regOdo S pOdd pEven (regsAt w).2 false
  let Qh := regOdo S aOdd aEven (regsAt w).2 false
  let corr : Bool := decide (w.getLast? = some Digit.two)
  let Sp := (altShifts (W1Odd w) (vP2 w) (vQ1 w)).1
  let cP := altP0Coeff (W1Odd w) .dsP1Plus
  let cM := altP0Coeff (W1Odd w) .dsP1Minus
  let c1 := altP0Coeff (W1Odd w) .q1Plus
  let c2 := altP0Coeff (W1Odd w) .q1Minus
  [stdPiece P (altOff w cP) (altAff w cP),
    stdPiece (if corr then lOdd w.dropLast false true else P) (altOff w cP + Sp) (altAff w cP + aP2 w),
    stdPiece (if corr then lOdd w.dropLast true true else P) (altOff w cM) (altAff w cM),
    stdPiece P (altOff w cM + Sp) (altAff w cM + aP2 w),
    stdPiece Q (altOff w c1) (altAff w c1),
    stdPiece Q (altOff w c2) (altAff w c2)] ++
  (match (altTypeOf w).bind (fun ty => altQ1Coeff (W1Odd w) ty) with
    | none => []
    | some c => [stdPiece Qh (altOff w c) (altAff w c)])

/-- The decomposition of the even alternate tile odometer of `w` (`eq:alt_odometer_decomposition`, second line): the odd
register twice, two copies of the even register for each shifted doubling (shift `S_q`, affine factor plus `a_{p_1,2}`), and the
alternate parent `ô(p_1)` when the type of `w` keeps it. After a `3` the first copy of `+` is `o^{L,+}_{q_1}` and the second copy
of `-` is `o^{L,-}_{q_1}` (`T(q_1)^{+,1}`, `T(q_1)^{-,2}` in both orientations, line 3995), elongated. -/
def tileAltEvenPieces (S : WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer)
    (lEven : Word → Bool → Bool → PartialOdometer) (w : Word) : List Piece :=
  let P := regOdo S pOdd pEven (regsAt w).1 true
  let Q := regOdo S pOdd pEven (regsAt w).2 false
  let Ph := regOdo S aOdd aEven (regsAt w).1 true
  let corr : Bool := decide (w.getLast? = some Digit.three)
  let Sq := (altShifts (W1Odd w) (vP2 w) (vQ1 w)).2
  let cP := altQ0Coeff (W1Odd w) .dsQ1Plus
  let cM := altQ0Coeff (W1Odd w) .dsQ1Minus
  let c1 := altQ0Coeff (W1Odd w) .p1Plus
  let c2 := altQ0Coeff (W1Odd w) .p1Minus
  [stdPiece (if corr then lEven w.dropLast true true else Q) (altOff w cP) (altAff w cP),
    stdPiece Q (altOff w cP + Sq) (altAff w cP + aP2 w),
    stdPiece Q (altOff w cM) (altAff w cM),
    stdPiece (if corr then lEven w.dropLast false true else Q) (altOff w cM + Sq) (altAff w cM + aP2 w),
    stdPiece P (altOff w c1) (altAff w c1),
    stdPiece P (altOff w c2) (altAff w c2)] ++
  (match (altTypeOf w).bind (fun ty => altP1Coeff (W1Odd w) ty) with
    | none => []
    | some c => [stdPiece Ph (altOff w c) (altAff w c)])

/-! ### The L-corrections as decompositions (`def:odd_l_correction`, `def:even_l_correction`, `lemma:l_correct_existence`) -/

/-- The printed `K_1, ..., K_4` of the odd L-correction as coefficient vectors `(c_{p,1}, c_{p,2}, c_{q,1}, c_{q,2})`. -/
def oddKCoeff (odd plus : Bool) : AltCoeff × AltCoeff × AltCoeff × AltCoeff :=
  match odd, plus with
  | true, true => ((0, 0, 0, 1), (-1, 0, 1, 1), (1, 1, -1, -1), (0, 0, -1, 0))
  | true, false => ((0, 0, 0, -1), (0, -1, 0, 0), (1, 0, -1, 0), (0, 0, 1, 0))
  | false, true => ((0, 0, 0, 1), (0, 0, 0, 1), (0, 1, 0, -1), (0, 0, 1, 0))
  | false, false => ((0, 0, 0, -1), (-1, -1, 1, 0), (0, 0, 0, 0), (0, 0, -1, 0))

/-- The printed `K_1, ..., K_4` of the even L-correction as coefficient vectors (`s = 2` when `s2`). -/
def evenKCoeff (odd plus s2 : Bool) : AltCoeff × AltCoeff × AltCoeff × AltCoeff :=
  match odd, plus with
  | true, true => ((1, 0, 0, 0), (1, 0, 0, 0), if s2 then (-1, -1, 2, 1) else (-1, 0, 1, 0), (0, 1, 0, 0))
  | false, true => ((-1, 0, 0, 0), (0, 0, -1, 0), if s2 then (0, -1, 0, 1) else (1, 0, -1, 0), (0, 1, 0, 0))
  | true, false => ((-1, 0, 0, 0), (0, 1, -1, -1), if s2 then (0, -1, 1, 1) else (0, 0, 0, 0), (0, -1, 0, 0))
  | false, false => ((1, 0, 0, 0), (1, 1, 0, -1), if s2 then (-1, -1, 1, 1) else (0, 0, 0, 0), (0, -1, 0, 0))

/-- The coefficient vectors give the K-table of `LCorrections` (`oddTexK`). -/
theorem oddKCoeff_spec (odd plus : Bool) (p q : Fraction) :
    coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) (oddKCoeff odd plus).1 =
        (LCorrections.oddTexK odd plus p q).1 ∧
      coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) (oddKCoeff odd plus).2.1 =
        (LCorrections.oddTexK odd plus p q).2.1 ∧
      coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) (oddKCoeff odd plus).2.2.1 =
        (LCorrections.oddTexK odd plus p q).2.2.1 ∧
      coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) (oddKCoeff odd plus).2.2.2 =
        (LCorrections.oddTexK odd plus p q).2.2.2 := by
  cases odd <;> cases plus <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;>
    simp [oddKCoeff, LCorrections.oddTexK, coeffOff, texV1Odd, texV1Even, texV2] <;> ring

/-- The coefficient vectors give the K-table of `LCorrections` (`evenTexK`). -/
theorem evenKCoeff_spec (odd plus s2 : Bool) (p q : Fraction) :
    coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) (evenKCoeff odd plus s2).1 =
        (LCorrections.evenTexK odd plus s2 p q).1 ∧
      coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) (evenKCoeff odd plus s2).2.1 =
        (LCorrections.evenTexK odd plus s2 p q).2.1 ∧
      coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) (evenKCoeff odd plus s2).2.2.1 =
        (LCorrections.evenTexK odd plus s2 p q).2.2.1 ∧
      coeffOff (texV1Odd p) (texV2 p) (texV1Even q) (texV2 q) (evenKCoeff odd plus s2).2.2.2 =
        (LCorrections.evenTexK odd plus s2 p q).2.2.2 := by
  cases odd <;> cases plus <;> cases s2 <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> ext <;>
    simp [evenKCoeff, LCorrections.evenTexK, coeffOff, texV1Odd, texV1Even, texV2] <;> ring

/-- The initial offset of the odd L-correction of the odd child of `w`, in the frame of that child: the outer copy
`T(q_1)^{+,2}` (case `10`), `T(q_1)^{-,1}` (`11`), `T(q_1)^{+,1}` (`00`), `T(q_1)^{-,2}` (`01`) of its decomposition. -/
def oddLInitOff (w : Word) (plus : Bool) : Site :=
  if W1Odd w then (if plus then p0Off w .q1DPlus + vQ1 w else p0Off w .q1DMinus)
  else (if plus then p0Off w .q1DPlus else p0Off w .q1DMinus + vQ1 w)

/-- The affine factor of that copy. -/
def oddLInitAff (w : Word) (plus : Bool) : Site := if plus then p0Aff w .q1DPlus else p0Aff w .q1DMinus

/-- The initial offset of the even L-correction of the even child of `w`: the outer copy `T(p_1)^{+,1}` (`x0`) or
`T(p_1)^{-,2}` (`x1`) of its decomposition. -/
def evenLInitOff (w : Word) (plus : Bool) : Site :=
  if plus then q0Off w .p1DPlus else q0Off w .p1DMinus + vP2 w

/-- The affine factor of that copy. -/
def evenLInitAff (w : Word) (plus : Bool) : Site :=
  if plus then q0Aff w .p1DPlus else q0Aff w .p1DMinus + aP2 w

/-- The enlarged one-odometer `o^d_{1/1}` on `T^d_{1/1}` (line 1558). -/
def enlOdo : PartialOdometer := ⟨(tileShape ZTile.oneD).toFinset, zTileOdo ZTile.oneD⟩

/-- The pieces of the odd L-corrected odometer `o^{L,±}_{p_0}` of the odd child of `w = w_1 s 2^k` (`pre = w_1 s`, `p_2, q_2` the
parents of `pre`), in the frame of the child: the stems `T(q_2) + j K_1` (`0 ≤ j ≤ k`), the bridge `T(p_2)` at `k K_1 + K_2`
(shifted by `oddBridgeShift` when `pre = 3^j`), and the heads `T̂(q_2)` at `k K_1 + K_2 + K_3 + i K_4` (`1 ≤ i ≤ 2(k+1) - z`,
`z = 0` when elongated). The first head is exempt at the points of the set `A` of `lemma:basecase_3k_even_alt` (with
`d = 2j + 1`) that lie in the last stem, when `pre = 3^j`. -/
def oddLPieces (S : WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer) (w : Word) (plus elong : Bool) :
    List Piece :=
  let pre := stripTrailing Digit.two w
  let k := trailingCount Digit.two w
  let o := W1Odd w
  let K := oddKCoeff o plus
  let o0 := oddLInitOff w plus
  let a0 := oddLInitAff w plus
  let triple : Bool := !pre.isEmpty && pre.all (fun d => decide (d = Digit.three))
  let stem := regOdo S pOdd pEven (regsAt pre).2 false
  let bridge := regOdo S pOdd pEven (regsAt pre).1 true
  let head := regOdo S aOdd aEven (regsAt pre).2 false
  let cB : AltCoeff := (k : ℤ) • K.1 + K.2.1
  let nh := 2 * (k + 1) - (if elong then 0 else 1)
  let stemK : Finset Site := stem.dom.image (· + (o0 + altOff pre ((k : ℤ) • K.1)))
  let hc : ℕ → AltCoeff := fun i => cB + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2
  (List.range (k + 1)).map (fun (j : ℕ) => stdPiece stem (o0 + altOff pre ((j : ℤ) • K.1)) (a0 + altAff pre ((j : ℤ) • K.1))) ++
    [stdPiece bridge (o0 + altOff pre cB + LCorrections.oddBridgeShift triple o plus) (a0 + altAff pre cB)] ++
    (List.range nh).map (fun (i : ℕ) =>
      { odo := head, off := o0 + altOff pre (hc i), aff := a0 + altAff pre (hc i),
        exc := if triple && i == 0 then
          {x | x - (o0 + altOff pre (hc 0)) ∈ paperStairAltA (2 * (pre.length : ℤ) + 1) ∧ x ∈ stemK} else ∅ })

/-- The pieces of the even L-corrected odometer `o^{L,±}_{q_0}` of the even child of `w = w_1 s 3^k`: the stems `T(p_2) + j K_1`,
the bridge `T(q_2)` at `k K_1 + K_2`, and when `pre = 2^j` the copy of `T^d_{1/1}` at `k K_1 + K_2 + 1 + i` (replacing the bridge in
case `01`), then the heads `T̂(p_2)`. The first head is exempt at the points of the set `A` of `lemma:basecase_2k_odd_alt` (in the
frame translated by `-e_2`, `d = 2j + 1`) that lie in the last stem, when `pre = 2^j`. -/
def evenLPieces (S : WeakData) (pOdd pEven aOdd aEven : Word → PartialOdometer) (w : Word) (plus elong : Bool) :
    List Piece :=
  let pre := stripTrailing Digit.three w
  let k := trailingCount Digit.three w
  let o := W1Odd w
  let s2 : Bool := decide (pre.getLast? = some Digit.two)
  let K := evenKCoeff o plus s2
  let o0 := evenLInitOff w plus
  let a0 := evenLInitAff w plus
  let double : Bool := !pre.isEmpty && pre.all (fun d => decide (d = Digit.two))
  let case01 : Bool := !o && !plus
  let stem := regOdo S pOdd pEven (regsAt pre).1 true
  let bridge := regOdo S pOdd pEven (regsAt pre).2 false
  let head := regOdo S aOdd aEven (regsAt pre).1 true
  let cB : AltCoeff := (k : ℤ) • K.1 + K.2.1
  let nh := 2 * (k + 1) - (if elong then 0 else 1)
  let stemK : Finset Site := stem.dom.image (· + (o0 + altOff pre ((k : ℤ) • K.1)))
  let hc : ℕ → AltCoeff := fun i => cB + K.2.2.1 + ((i : ℤ) + 1) • K.2.2.2
  (List.range (k + 1)).map (fun (j : ℕ) => stdPiece stem (o0 + altOff pre ((j : ℤ) • K.1)) (a0 + altAff pre ((j : ℤ) • K.1))) ++
    (if double && case01 then [] else [stdPiece bridge (o0 + altOff pre cB) (a0 + altAff pre cB)]) ++
    (if double then [stdPiece enlOdo (o0 + altOff pre cB + ((1 : ℤ), (1 : ℤ))) (a0 + altAff pre cB)] else []) ++
    (List.range nh).map (fun (i : ℕ) =>
      { odo := head, off := o0 + altOff pre (hc i), aff := a0 + altAff pre (hc i),
        exc := if double && i == 0 then
          {x | x - (o0 + altOff pre (hc 0)) + ((0 : ℤ), (1 : ℤ)) ∈ paperNearStairAltA (2 * (pre.length : ℤ) + 1) ∧
            x ∈ stemK} else ∅ })

/-- The orientation and the reversal of the string of a side (as in `RespectsAnchored`). -/
def sideOrient : Side → Orientation × Bool
  | .hPlus => (.horizontal, false)
  | .hMinus => (.horizontal, true)
  | .vPlus => (.vertical, false)
  | .vMinus => (.vertical, true)

/-- The L-corrected odometer `L` respects the strings of the given sides of the child tile (anchored at `c(T) = 0`), and agrees
with the tile odometer `T` of the child there up to one constant (`lemma:l_correct_existence`, last sentence of its proof). -/
def LSidesAgree (L T : PartialOdometer) (wh wv : BinaryWord) (sides : List Side) : Prop :=
  (∀ s ∈ sides, RespectsTiles (sideOrient s).1 (sideOrient s).2 (sideString wh wv 0 s) L.val) ∧
    ∃ c : ℤ, ∀ s ∈ sides, ∀ x ∈ placedSites (sideString wh wv 0 s), x ∈ L.dom ∧ x ∈ T.dom ∧ L.val x = T.val x + c

/-- The sides of `lemma:l_correc_properties` (2) for the elongated even L-correction, by case (`W_1` odd, `+`): `10`: `w_h, w_v`;
`00`: `w_h, rev w_v`; `11`: `rev w_h, rev w_v`; `01`: `rev w_h, w_v`. -/
def printedEvenSides (odd plus : Bool) : List Side :=
  match odd, plus with
  | true, true => [.hPlus, .vPlus]
  | false, true => [.hPlus, .vMinus]
  | true, false => [.hMinus, .vMinus]
  | false, false => [.hMinus, .vPlus]

/-- The sides of the child tile that each L-correction contains (`lSides oddChild W1odd plus elongated`). The elongated even
correction has the printed sides of `lemma:l_correc_properties` (2) (`printedEvenSides`); a short correction has the one side of its
partial tile (`T^{h±}(q_0)`, and `T^{v±}(p_0)` with `+` and `-` flipped when `W_1` is even, `def:odd_l_correction`,
`def:even_l_correction`); the elongated odd correction has that `v` side and the `h` side opposite to its sign. The containment of
these strings in the cells of the L-correction holds for every word of length at most 5 and no other side is contained for every
word (numerics, `tmp-w6/chk3.py`); it is not proved here. -/
def paperLSides (oddChild odd plus elong : Bool) : List Side :=
  if oddChild then
    (if elong then [if plus then .hMinus else .hPlus] else []) ++ [if odd == plus then .vPlus else .vMinus]
  else
    if elong then printedEvenSides odd plus else [if plus then .hPlus else .hMinus]

/-! ### The properties: (c) of `lemma:weak_standard_odometer_properties`, (a)-(c) of `lemma:tile-odometer-existence` -/

/-- `h_0` of `eq:harmonic_h0` (`Plane.SurgicalH0`). -/
def h0 (x : Site) : ℤ := -centeredQuarterTurnCorrection x

/-- `o - α^T x - β`. -/
def normed (o : PartialOdometer) (α : Site) (β : ℤ) (x : Site) : ℤ := o.val x - dotS α x - β

/-- The normalisation of `lemma:tile-odometer-existence`: with `c(T) = 0`, `o - α^T x - β = o_{1/1}` on the first tile
`A = T_{1/1}` at the origin. -/
def FirstTileNormal (o : PartialOdometer) (α : Site) (β : ℤ) : Prop :=
  ∀ x ∈ tileShape ZTile.one, x ∈ o.dom ∧ normed o α β x = zTileOdo ZTile.one x

/-- (c) of `lemma:weak_standard_odometer_properties` for the lattice vector `v` with affine factor `a`: `o` and its lattice
adjacent translate are compatible, `o(x + v) - o(x) - a^T x` is constant where both points are in the domain. -/
def LatticeSelfCompatible (o : PartialOdometer) (v a : Site) : Prop :=
  ∃ c : ℤ, ∀ x, x ∈ o.dom → x + v ∈ o.dom → o.val (x + v) - o.val x - dotS a x = c

/-- (a) of `lemma:tile-odometer-existence`: normalised, `o(x + v_1) = o(x)` and `o(x + v_2) = o(x) + a_2^T x - h_0(v_2)` on the
intersections. -/
def TileTranslation (o : PartialOdometer) (v1 v2 a2 : Site) : Prop :=
  ∃ (α : Site) (β : ℤ), FirstTileNormal o α β ∧
    (∀ x, x ∈ o.dom → x + v1 ∈ o.dom → normed o α β (x + v1) = normed o α β x) ∧
    (∀ x, x ∈ o.dom → x + v2 ∈ o.dom → normed o α β (x + v2) = normed o α β x + dotS a2 x - h0 v2)

/-- (b) of `lemma:tile-odometer-existence` for a standard tile: with `D = v_1 + v_2 + 1 - i`, normalised,
`o(D - x) - o(x) = a_2^T (D/2 - x)` for `x` in the tile (both sides doubled). -/
def TileHalfTurn (o : PartialOdometer) (v1 v2 a2 : Site) : Prop :=
  ∃ (α : Site) (β : ℤ), FirstTileNormal o α β ∧
    ∀ x ∈ o.dom, (v1 + v2 + ((1 : ℤ), (-1 : ℤ))) - x ∈ o.dom ∧
      2 * (normed o α β ((v1 + v2 + ((1 : ℤ), (-1 : ℤ))) - x) - normed o α β x) =
        dotS a2 (v1 + v2 + ((1 : ℤ), (-1 : ℤ))) - 2 * dotS a2 x

/-- (b) of `lemma:tile-odometer-existence` for an alternate tile: `ô(D̂ - x) - ô(x) = Ê^T (D̂/2 - x)`, normalised. -/
def AltHalfTurn (o : PartialOdometer) (Dh E : Site) : Prop :=
  ∃ (α : Site) (β : ℤ), FirstTileNormal o α β ∧
    ∀ x ∈ o.dom, Dh - x ∈ o.dom ∧ 2 * (normed o α β (Dh - x) - normed o α β x) = dotS E Dh - 2 * dotS E x

/-- (c) of `lemma:tile-odometer-existence` for standard tiles: normalised, `o_{R(n/d)}(x) = o_{n/d}(i x + v_{n/d,1} - i) - h_0(x)`
on `T(R(n/d))`. -/
def TileRotation (o oR : PartialOdometer) (v1 : Site) : Prop :=
  ∃ (α : Site) (β : ℤ) (α' : Site) (β' : ℤ), FirstTileNormal o α β ∧ FirstTileNormal oR α' β' ∧
    ∀ x ∈ oR.dom, mulI x + v1 - ((0 : ℤ), (1 : ℤ)) ∈ o.dom ∧
      normed oR α' β' x = normed o α β (mulI x + v1 - ((0 : ℤ), (1 : ℤ))) - h0 x

/-- (c) of `lemma:tile-odometer-existence` for alternate tiles: `ô_{R(n/d)}(x) = ô_{n/d}(i x + c_f) - h_0(x) + γ^T x + c_0`. -/
def AltRotation (o oR : PartialOdometer) (cf γ : Site) : Prop :=
  ∃ (α : Site) (β : ℤ) (α' : Site) (β' : ℤ) (c0 : ℤ), FirstTileNormal o α β ∧ FirstTileNormal oR α' β' ∧
    ∀ x ∈ oR.dom, mulI x + cf ∈ o.dom ∧ normed oR α' β' x = normed o α β (mulI x + cf) - h0 x + dotS γ x + c0

/-- `D̂_{n/d}` of (b): `v_{p_1,1} + 2 v_{p_1,2} + v_{q_1,2} + 1 - i` for `q_0` even-first or `p_0` odd-first, and
`v_{p_1,1} + 2 v_{p_1,2} + 2 v_{q_1,1} + v_{q_1,2} + 1 - i` otherwise (`oddChild`: `n/d = p_0`). -/
def altD (w : Word) (oddChild : Bool) : Site :=
  if oddChild == W1Odd w then vP1 w + (2 : ℤ) • vP2 w + vQ2 w + ((1 : ℤ), (-1 : ℤ))
  else vP1 w + (2 : ℤ) • vP2 w + (2 : ℤ) • vQ1 w + vQ2 w + ((1 : ℤ), (-1 : ℤ))

/-- `Ê = 2 a_{p_1,2} + a_{q_1,2}`. -/
def altE (w : Word) : Site := (2 : ℤ) • aP2 w + aQ2 w

/-- `(c_f, γ)` of (c): for even `q_0`, `(v_{p_1,1} + v_{q_1,1} - i, 0)` even-first and
`(v_{p_1,1} + v_{p_1,2} + 2 v_{q_1,1} - i, i a_{p_1,2})` odd-first; for odd `p_0`, `(v_{p_0,1} + v_{p_1,2} - i, i a_{p_1,2})`
even-first and `(v_{p_0,1} - v_{q_1,1} - i, 0)` odd-first. -/
def altCf (w : Word) (oddChild : Bool) : Site × Site :=
  let vp0 := texV1Odd ((parentsAt w).current .odd)
  if oddChild then
    (if W1Odd w then (vp0 - vQ1 w - ((0 : ℤ), (1 : ℤ)), 0) else (vp0 + vP2 w - ((0 : ℤ), (1 : ℤ)), mulI (aP2 w)))
  else
    (if W1Odd w then (vP1 w + vP2 w + (2 : ℤ) • vQ1 w - ((0 : ℤ), (1 : ℤ)), mulI (aP2 w))
      else (vP1 w + vQ1 w - ((0 : ℤ), (1 : ℤ)), 0))

/-! ### The joint family -/

/-- The odometers of one word: weak standard (`wOdd`, `wEven`), weak alternate (`waOdd`, `waEven`), standard tile (`tOdd`,
`tEven`), alternate tile (`aOdd`, `aEven`), and the L-corrected odometers of the two children (`lOdd plus elongated`,
`lEven plus elongated`; meaningful when the L-correction is defined). -/
structure JSlice where
  wOdd : PartialOdometer
  wEven : PartialOdometer
  waOdd : PartialOdometer
  waEven : PartialOdometer
  tOdd : PartialOdometer
  tEven : PartialOdometer
  aOdd : PartialOdometer
  aEven : PartialOdometer
  lOdd : Bool → Bool → PartialOdometer
  lEven : Bool → Bool → PartialOdometer

/-- The empty slice. -/
instance : Inhabited JSlice :=
  ⟨let o : PartialOdometer := ⟨∅, fun _ => 0⟩; ⟨o, o, o, o, o, o, o, o, fun _ _ => o, fun _ _ => o⟩⟩

/-- The data the family reads: the weak data (initial odometers, boundary and partial tiles, base condition), the alternate
boundary tiles, base condition and anchors, and the sides on which an L-corrected odometer agrees with its child
(`lSides oddChild W1odd plus elongated`). -/
structure JointData where
  S : WeakData
  altBdry : Option Word → Bool → Finset Site
  altBase : Word → PartialOdometer → PartialOdometer → Prop
  anc : AltAnchors
  lSides : Bool → Bool → Bool → Bool → List Side

/-- The alternate boundary tiles of the text: the printed alternate tiles `SurgicalAltTiles.altOddTile` and `altEvenTile` over the
base alternates `PaperAltBase.paperAltBaseTiles` (which is `AltRotStep.B`). At the base words they are the domains that
`PaperAltBaseCond` fixes (`PaperAltDomains.altBase_domains`). -/
def PaperAltBdry (D : JointData) : Prop :=
  ∀ w : Word, D.altBdry (some w) true = SurgicalAltTiles.altOddTile PaperAltBase.paperAltBaseTiles w ∧
    D.altBdry (some w) false = SurgicalAltTiles.altEvenTile PaperAltBase.paperAltBaseTiles w

/-- The family restricted to the words shorter than `w` (empty elsewhere): every node at `w` reads its parents through it. -/
def below (f : Word → JSlice) (w : Word) : Word → JSlice :=
  fun u => if u.length < w.length then f u else default

/-- (1) The weak standard step at `w`, with the parent odometers `g` (the family below `w`): the domains are the boundary tiles; a
base word satisfies `S.base`; any other word has the standard decompositions from the TILE parents (`OddNodeP`, `EvenNodeP`);
(a) of `lemma:weak_standard_odometer_properties` (`RespectsAnchored`) at the children that are not corrected. At a corrected child
the tile odometer is the L-decomposition, which carries (a) itself (`TilePart`), and the weak child need not respect the strings:
the glue on the kept parts fails it at `w = 2 3^k`. -/
def WeakPart (D : JointData) (g : Word → JSlice) (w : Word) (wo we : PartialOdometer) : Prop :=
  wo.dom = D.S.bdry (some w) true ∧ we.dom = D.S.bdry (some w) false ∧
    (IsBase w → D.S.base w wo we) ∧
    (¬ IsBase w → OddNodeP D.S wo (fun u => (g u).tOdd) (fun u => (g u).tEven) w ∧
      EvenNodeP D.S we (fun u => (g u).tOdd) (fun u => (g u).tEven) w) ∧
    (¬ CorrectedAfterThree w → RespectsAnchored wo.dom (hWordOf w false) (vWordOf w false) wo.val) ∧
    (¬ CorrectedAfterTwo w → RespectsAnchored we.dom (hWordOf w true) (vWordOf w true) we.val)

/-- (2) The weak alternate step at `w`: the alternate decompositions from the tile parents and the alternate tile parents
(`AltOddNodeP`, `AltEvenNodeP`; base words: `altBase`), and (a) of `lemma:weak_alternate_odometer_properties`. -/
def WeakAltPart (D : JointData) (g : Word → JSlice) (w : Word) (wao wae : PartialOdometer) : Prop :=
  wao.dom = D.altBdry (some w) true ∧ wae.dom = D.altBdry (some w) false ∧
    (IsBase w → D.altBase w wao wae) ∧
    (¬ IsBase w →
      AltOddNodeP D.S wao (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven) w ∧
      AltEvenNodeP D.S wae (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd) (fun u => (g u).aEven) w) ∧
    RespectsHalfV (altRevVAnchor D.anc w) (vWordOf w false) wao.val ∧
    RespectsHalfH (altFwdHAnchor D.anc w) (hWordOf w true) wae.val

/-- (3) The tile step at `w` (definition of tile odometers): at a base word the tile odometers are the weak ones; otherwise each
is its decomposition from the tile parents and the L-corrected odometers of the parents; at an uncorrected child it is the weak
odometer; the tile odometers satisfy (a) of the weak lemma (`RespectsAnchored`, `RespectsHalfV`, `RespectsHalfH`); and the standard
tile odometers are defined on the standard tiles and the alternate tile odometers on the alternate tiles
(`lemma:tile-odometer-existence`; at a corrected child this is the identity of the corrected decomposition with the printed tile,
`LCorrecProps.CorrectedCells` and its alternate analogue). -/
def TilePart (D : JointData) (g : Word → JSlice) (w : Word) (wo we wao wae tod tev aod aev : PartialOdometer) : Prop :=
  (IsBase w → tod = wo ∧ tev = we ∧ aod = wao ∧ aev = wae) ∧
    (¬ IsBase w →
      RespectsPieces tod (tileOddPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).lEven) w) ∧
      RespectsPieces tev (tileEvenPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).lOdd) w) ∧
      RespectsPieces aod (tileAltOddPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd)
        (fun u => (g u).aEven) (fun u => (g u).lOdd) w) ∧
      RespectsPieces aev (tileAltEvenPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd)
        (fun u => (g u).aEven) (fun u => (g u).lEven) w)) ∧
    (¬ CorrectedAfterThree w → tod = wo ∧ aev = wae) ∧
    (¬ CorrectedAfterTwo w → tev = we ∧ aod = wao) ∧
    RespectsAnchored tod.dom (hWordOf w false) (vWordOf w false) tod.val ∧
    RespectsAnchored tev.dom (hWordOf w true) (vWordOf w true) tev.val ∧
    RespectsHalfV (altRevVAnchor D.anc w) (vWordOf w false) aod.val ∧
    RespectsHalfH (altFwdHAnchor D.anc w) (hWordOf w true) aev.val ∧
    tod.dom = D.S.bdry (some w) true ∧ tev.dom = D.S.bdry (some w) false ∧
    aod.dom = D.altBdry (some w) true ∧ aev.dom = D.altBdry (some w) false

/-- (4) The L-corrected odometers at `w` (`lemma:l_correct_existence`): when the L-correction is defined, the decomposition from
the tile odometers of the parents of `w_1 s` and the alternate tile odometers (`oddLPieces`, `evenLPieces`), and the agreement with
the tile odometer of the child on the sides `lSides`. -/
def LPart (D : JointData) (g : Word → JSlice) (w : Word) (tod tev : PartialOdometer)
    (lo le : Bool → Bool → PartialOdometer) : Prop :=
  (∀ plus elong : Bool, OddLDefined w →
      RespectsPieces (lo plus elong) (oddLPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd)
        (fun u => (g u).aEven) w plus elong) ∧
      LSidesAgree (lo plus elong) tod (hWordOf w false) (vWordOf w false) (D.lSides true (W1Odd w) plus elong)) ∧
    (∀ plus elong : Bool, EvenLDefined w →
      RespectsPieces (le plus elong) (evenLPieces D.S (fun u => (g u).tOdd) (fun u => (g u).tEven) (fun u => (g u).aOdd)
        (fun u => (g u).aEven) w plus elong) ∧
      LSidesAgree (le plus elong) tev (hWordOf w true) (vWordOf w true) (D.lSides false (W1Odd w) plus elong))

/-- The joint predicate at the word `w`: the four parts, over the family restricted to the shorter words (`below f w`). -/
def IsJointSlice (D : JointData) (f : Word → JSlice) (w : Word) : Prop :=
  WeakPart D (below f w) w (f w).wOdd (f w).wEven ∧
    WeakAltPart D (below f w) w (f w).waOdd (f w).waEven ∧
    TilePart D (below f w) w (f w).wOdd (f w).wEven (f w).waOdd (f w).waEven (f w).tOdd (f w).tEven (f w).aOdd
      (f w).aEven ∧
    LPart D (below f w) w (f w).tOdd (f w).tEven (f w).lOdd (f w).lEven

/-- (c) of `lemma:weak_standard_odometer_properties` at `w`: each weak odometer is compatible with its lattice adjacent
translates, for both lattice vectors of the child. -/
def WeakProps (w : Word) (wo we : PartialOdometer) : Prop :=
  let p0 := (parentsAt w).current .odd
  let q0 := (parentsAt w).current .even
  LatticeSelfCompatible wo (texV1Odd p0) 0 ∧ LatticeSelfCompatible wo (texV2 p0) (offsetA p0.num p0.den true) ∧
    LatticeSelfCompatible we (texV1Even q0) 0 ∧ LatticeSelfCompatible we (texV2 q0) (offsetA q0.num q0.den true)

/-- (c) of `lemma:weak_standard_odometer_properties` at `w`, at the children that are not corrected (the property the joint family
carries). At a corrected child the tile odometer is the L-decomposition and (c) of the weak child is not used; it follows from (a)
(`LatticeOfRespects.weakProps_of_respects`), which the glue on the kept parts fails at `w = 2 3^k`. -/
def WeakPropsU (w : Word) (wo we : PartialOdometer) : Prop :=
  let p0 := (parentsAt w).current .odd
  let q0 := (parentsAt w).current .even
  (¬ CorrectedAfterThree w →
      LatticeSelfCompatible wo (texV1Odd p0) 0 ∧ LatticeSelfCompatible wo (texV2 p0) (offsetA p0.num p0.den true)) ∧
    (¬ CorrectedAfterTwo w →
      LatticeSelfCompatible we (texV1Even q0) 0 ∧ LatticeSelfCompatible we (texV2 q0) (offsetA q0.num q0.den true))

theorem weakPropsU_of_weakProps (w : Word) (wo we : PartialOdometer) (h : WeakProps w wo we) : WeakPropsU w wo we := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨fun _ => ⟨h1, h2⟩, fun _ => ⟨h3, h4⟩⟩

/-- (b) of `lemma:weak_alternate_odometer_properties` for an odometer `ao` of the odd alternate child `p_0` of `w`: `ao` is
compatible with its lattice adjacent translates along both generators of `L'(p_0)`, `v_{p_0,1}` with affine factor `0` and
`v_{p_0,2}` with affine factor `a_{p_0,2}`. -/
def AltLatticeOdd (w : Word) (ao : PartialOdometer) : Prop :=
  let p0 := (parentsAt w).current .odd
  LatticeSelfCompatible ao (texV1Odd p0) 0 ∧ LatticeSelfCompatible ao (texV2 p0) (offsetA p0.num p0.den true)

/-- (b) of `lemma:weak_alternate_odometer_properties` for an odometer `ae` of the even alternate child `q_0` of `w`, along
`v_{q_0,1}` (affine factor `0`) and `v_{q_0,2}` (affine factor `a_{q_0,2}`). -/
def AltLatticeEven (w : Word) (ae : PartialOdometer) : Prop :=
  let q0 := (parentsAt w).current .even
  LatticeSelfCompatible ae (texV1Even q0) 0 ∧ LatticeSelfCompatible ae (texV2 q0) (offsetA q0.num q0.den true)

/-- (b) of `lemma:weak_alternate_odometer_properties` at `w` for a pair of alternate odometers of the two alternate children of
`w`: lattice adjacent alternate odometers are compatible. The joint family carries it for the alternate tile odometers
(`JointProps`), which the tile decompositions read as the alternate parents (Case 3) and the L-corrections read as their heads; at a
corrected alternate child the alternate tile odometer is the L-decomposition (the alternate parent of the odd alternate child of
`133` is the even alternate tile odometer of `13`, corrected after a `3`). -/
def AltLatticeSelfCompat (w : Word) (ao ae : PartialOdometer) : Prop :=
  AltLatticeOdd w ao ∧ AltLatticeEven w ae

/-- (b) of `lemma:weak_alternate_odometer_properties` at `w` for the weak alternate odometers, at the alternate children that are
not corrected, where they are the alternate tile odometers (`TilePart`): the odd alternate child unless `w` ends in a `2`, the
even alternate child unless it ends in a `3`. -/
def WeakAltPropsU (w : Word) (wao wae : PartialOdometer) : Prop :=
  (¬ CorrectedAfterTwo w → AltLatticeOdd w wao) ∧ (¬ CorrectedAfterThree w → AltLatticeEven w wae)

/-- (a) and (b) of `lemma:tile-odometer-existence` at `w`. -/
def TileProps (w : Word) (tod tev aod aev : PartialOdometer) : Prop :=
  let p0 := (parentsAt w).current .odd
  let q0 := (parentsAt w).current .even
  TileTranslation tod (texV1Odd p0) (texV2 p0) (offsetA p0.num p0.den true) ∧
    TileTranslation tev (texV1Even q0) (texV2 q0) (offsetA q0.num q0.den true) ∧
    TileHalfTurn tod (texV1Odd p0) (texV2 p0) (offsetA p0.num p0.den true) ∧
    TileHalfTurn tev (texV1Even q0) (texV2 q0) (offsetA q0.num q0.den true) ∧
    AltHalfTurn aod (altD w true) (altE w) ∧ AltHalfTurn aev (altD w false) (altE w)

/-- (c) of `lemma:tile-odometer-existence` at `w`: the tile odometers of the children of `w` against those of the rotated children,
of the other parity, at `swapW w` (`rot_standard_tiles`). -/
def RotProps (w : Word) (x r : JSlice) : Prop :=
  TileRotation x.tOdd r.tEven (texV1Odd ((parentsAt w).current .odd)) ∧
    TileRotation x.tEven r.tOdd (texV1Even ((parentsAt w).current .even)) ∧
    AltRotation x.aOdd r.aEven (altCf w true).1 (altCf w true).2 ∧
    AltRotation x.aEven r.aOdd (altCf w false).1 (altCf w false).2

/-- The rotation of an L-corrected odometer (the odometer form of `lemma:l_correc_properties` (1), implicit in "rotating the
decomposition"): with no normalisation of the L-corrected odometers, `o_R(y) = o(i y + v_{n/d,1} - i) - h_0(y) + c_0` on the
rotated domain. There is no affine term: each L-corrected odometer agrees with its child on the sides up to a constant, and the
children rotate with no affine term. -/
def LRotation (o oR : PartialOdometer) (v1 : Site) : Prop :=
  ∃ c0 : ℤ, ∀ y ∈ oR.dom, mulI y + v1 - ((0 : ℤ), (1 : ℤ)) ∈ o.dom ∧
    oR.val y = o.val (mulI y + v1 - ((0 : ℤ), (1 : ℤ))) - h0 y + c0

/-- The rotation identities of the L-corrected odometers at `w` against those of the rotated children at `swapW w`, with the signs
of `lemma:l_correc_properties` (1) (numerics, words of length at most 3, both elongations). -/
def LRotProps (w : Word) (x r : JSlice) : Prop :=
  (EvenLDefined w → ∀ plus elong : Bool,
    LRotation (x.lEven plus elong) (r.lOdd (plus != W1Odd w) elong) (texV1Even ((parentsAt w).current .even))) ∧
  (OddLDefined w → ∀ plus elong : Bool,
    LRotation (x.lOdd plus elong) (r.lEven (plus == W1Odd w) elong) (texV1Odd ((parentsAt w).current .odd)))

/-- The properties at `w` proved by the induction. The last is (b) of `lemma:weak_alternate_odometer_properties` for the
alternate tile odometers. -/
def JointProps (f : Word → JSlice) (w : Word) : Prop :=
  WeakPropsU w (f w).wOdd (f w).wEven ∧ TileProps w (f w).tOdd (f w).tEven (f w).aOdd (f w).aEven ∧
    RotProps w (f w) (f (swapW w)) ∧ LRotProps w (f w) (f (swapW w)) ∧ AltLatticeSelfCompat w (f w).aOdd (f w).aEven

/-- The joint family: the joint predicate and the properties at every word. -/
def IsJointFamily (D : JointData) (f : Word → JSlice) : Prop :=
  ∀ w : Word, IsJointSlice D f w ∧ JointProps f w

/-! ### The cells of the even L-correction (w2), kept for the comparison with `LCorrections` -/

/-- The L-corrected domain of the even child `T(q_0)` of `w = w_1 s 3^k` from the cell sets of `LCorrections`, with the alternate
base `altBase`, translated by the initial offset `off w plus`. -/
def evenCell (altBase : Word → Standard.Tile × Standard.Tile) (off : Word → Bool → Site) (elong : Bool) (w : Word)
    (plus : Bool) : Finset Site :=
  let pre := stripTrailing Digit.three w
  let k := trailingCount Digit.three w
  let odd := phase pre == 1
  let s2 := decide (pre.getLast? = some Digit.two)
  let dbl := !pre.isEmpty && pre.all (fun d => decide (d = Digit.two))
  let st := Standard.stateAt pre
  let pq := LCorrections.wordParents pre
  LCorrections.shiftCells
    (LCorrections.evenLCorrection k elong dbl st.tOdd st.tEven
      (SurgicalAltTiles.altRegs altBase pre).1 (SiteStrings.baseSites Letter.q true).toFinset pq.1 pq.2 odd plus s2)
    (off w plus)

end FLatticePaper.Tiles.JointFamily
