import FLatticePaper.Tiles.SurgicalWeakOdometers
import FLatticePaper.Tiles.SurgicalDict
import FLatticePaper.Tiles.SurgicalCorners

/-! # The weak alternate odometers of the surgical edition (`def:alternate_doubled_tile`, `def:weak_alternate_odometers`)

The alternate tiles `T̂(p_0)`, `T̂(q_0)` have the alternate decomposition `eq:alt_decomp`: the odd alternate child is
`ds(o)_{p_1}^± ∪ o_{q_1}^± ∪ ô(q_1)` and the even one is `o_{p_1}^± ∪ ds(o)_{q_1}^± ∪ ô(p_1)`, where `ds(o)` are the weak
shifted doublings (`IsWeakDoubling`, shift `S_p`, `S_q` of `altShifts`), the plain pieces are the standard odometers of the
parents (`WeakData` registers), and `ô(q_1)`, `ô(p_1)` are the alternate parent odometers (the alternate registers).

Offsets are the printed tables `eq:alt_offsets_w1_odd/even` and the alternate parent positions of `def:alternate_tiles`,
written as coefficient vectors `(c_{p,1}, c_{p,2}, c_{q,1}, c_{q,2})`; a piece at offset `Σ c_i v_i` carries the affine factor
`Σ c_i a_i` (the operator's rule, `coeffAffine`). The parent piece is omitted in the printed `-` cases (type 2 for the odd
child, type 3 for the even child). Assumptions, to be confirmed: `odd-first` means `W_1` odd; the type `s` of a child is the
last letter of the word whose children are decomposed. -/

namespace FLatticePaper.Tiles.SurgicalAlt

open FLatticePaper.Farey
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SurgicalDict
open FLatticePaper.Tiles.SurgicalWeak

/-- A coefficient vector `(c_{p,1}, c_{p,2}, c_{q,1}, c_{q,2})` of the generators of an offset. -/
abbrev AltCoeff := ℤ × ℤ × ℤ × ℤ

/-- The offset `Σ c_i v_i` of a coefficient vector (`v_{p,1}, v_{p,2}, v_{q,1}, v_{q,2}`). -/
def coeffOff (vp1 vp2 vq1 vq2 : GInt) (c : AltCoeff) : GInt :=
  (c.1 * vp1.1 + c.2.1 * vp2.1 + c.2.2.1 * vq1.1 + c.2.2.2 * vq2.1,
    c.1 * vp1.2 + c.2.1 * vp2.2 + c.2.2.1 * vq1.2 + c.2.2.2 * vq2.2)

/-- The affine factor of a coefficient vector: `c_{p,2} a_{p,2} + c_{q,2} a_{q,2}` with `a_{r,2} = (n_r, -d_r)`
(`a_{r,1} = 0`). -/
def coeffAffine (np dp nq dq : ℤ) (c : AltCoeff) : GInt :=
  (c.2.1 * np + c.2.2.2 * nq, -(c.2.1 * dp + c.2.2.2 * dq))

/-- `c(T) - c(T̂(p_0))` of `eq:alt_offsets_w1_odd` (`odd = true`) and `eq:alt_offsets_w1_even`, for the pieces of `placeAltP0`. -/
def altP0Coeff (odd : Bool) : AltP0Piece → AltCoeff
  | .q1Plus => if odd then (1, 0, 0, 0) else (0, 0, 0, 0)
  | .q1Minus => if odd then (0, 2, -1, 0) else (1, 2, 1, 0)
  | .dsP1Plus => if odd then (0, 0, 0, 0) else (0, 0, 1, 0)
  | .dsP1Minus => if odd then (0, 0, 1, 1) else (0, 0, 0, 1)

/-- `c(T) - c(T̂(q_0))` of the two tables, for the pieces of `placeAltQ0`. -/
def altQ0Coeff (odd : Bool) : AltQ0Piece → AltCoeff
  | .dsQ1Plus => if odd then (1, 0, 0, 0) else (0, 0, 0, 0)
  | .dsQ1Minus => if odd then (0, 1, 0, 0) else (1, 1, 0, 0)
  | .p1Plus => if odd then (0, 0, 0, 0) else (0, 0, 1, 0)
  | .p1Minus => if odd then (0, 1, 2, 1) else (0, 1, -1, 1)

/-- `c(T̂(q_1)) - c(T̂(p_0))` (`def:alternate_tiles`): omitted for type `two`. -/
def altQ1Coeff (odd : Bool) (ty : Digit) : Option AltCoeff :=
  if ty = .two then none else if odd then some (1, 1, -1, 0) else some (0, 1, 1, 0)

/-- `c(T̂(p_1)) - c(T̂(q_0))` (`def:alternate_tiles`): omitted for type `three`. -/
def altP1Coeff (odd : Bool) (ty : Digit) : Option AltCoeff :=
  if odd then
    (if ty = .one then some (0, 1, 1, 0) else if ty = .two then some (0, 0, 2, 1) else none)
  else
    (if ty = .one then some (1, 1, -1, 0) else if ty = .two then some (0, 0, 0, 1) else none)

/-- The alternate type of the quadruple labelled by `w`: the last letter of `w`, where `w` labels `(p_0, q_0)` (the child
word, `oddO w`, `evenO w`), as the operator confirms for `def:alternate_tiles` (the children's own word; `w = w' * s` with `s`
selecting the parents). `W_1` is counted in the same `w` (`phase w`). -/
def altTypeOf (w : Word) : Option Digit := w.getLast?

/-- A parent piece at the offset of an optional coefficient vector (`none`: the piece is omitted). -/
def ParentPieceOk (parent child : PartialOdometer) (vp1 vp2 vq1 vq2 : GInt) (np dp nq dq : ℤ) :
    Option AltCoeff → Prop
  | none => True
  | some c => PlacedPiece parent child (coeffOff vp1 vp2 vq1 vq2 c) (coeffAffine np dp nq dq c)

/-- The partial tile of a doubled alternate piece: the L-correction `T^{L,±}` (`partialT`) when the piece is corrected, and the
boundary tile `T^b` on both copies otherwise (`def:alternate_doubled_tile`: the doubled pieces are corrected only in Type 2 for the
odd alternate child and Type 3 for the even one; otherwise both copies are full). -/
def altPartial (S : WeakData) (u : Option Word) (b corrected : Bool) (lab : Bool) : Finset Site :=
  if corrected then S.partialT u b lab else S.bdry u b

/-- The alternate weak doubling (`def:alternate_doubled_tile`, manuscript f9cf1c2), defined like `IsWeakDoublingStd`: the doubled
odometer `d = o ∪ o*` of `IsWeakDoublingOn` with the partial tile on the second copy (`firstPartial = false`) or on the first copy
(`firstPartial = true`), and, after restriction to the meeting string of the first copy (`meet`: the horizontal `rev(w_h)` for the
odd register `p`, the vertical `rev(w_v)` or `w_v` for `q` by the parity of `W_1`), `o*` and `o` respect the tile translations with
the affine factor of the shift (`a_{p,2}` for both `S_p` and `S_q`, so `i = true`, `(n, d) = (p.num, p.den)`). -/
def IsWeakDoublingAlt (firstPartial : Bool) (meet : FLatticePaper.Tiles.Side) (n d : ℤ) (i : Bool) (wh wv : BinaryWord)
    (Tb Th : Finset Site) (v : Site) (o dd : PartialOdometer) : Prop :=
  ∃ ostar : PartialOdometer,
    (if firstPartial then IsWeakDoublingOn Th Tb v o dd ostar else IsWeakDoublingOn Tb Th v o dd ostar) ∧
    FLatticePaper.Tiles.DoublingRespect.RespectsMeeting n d i wh wv meet v o ostar

/-- The alternate odd child `T̂(p_0)` of the word `w` (`eq:alt_decomp`, first line): the shifted doublings `ds(o)_{p_1}^±`
of the odd register (shift `S_p`), the plain pieces `o_{q_1}^±` of the even register, and the parent piece `ô(q_1)` of the even
alternate register (when the type of `w` is not `two`). -/
def AltOddNode (S : WeakData) (oddO evenO altOdd altEven : Word → PartialOdometer) (w : Word) : Prop :=
  ∃ dsp dsm : PartialOdometer,
    IsWeakDoublingAlt false FLatticePaper.Tiles.Side.hMinus (parentsAt w).odd.num (parentsAt w).odd.den true
        (FLatticePaper.Tiles.DoublingRespect.regWords true (regsAt w).1).1 (FLatticePaper.Tiles.DoublingRespect.regWords true (regsAt w).1).2
        (S.bdry (regsAt w).1 true) (altPartial S (regsAt w).1 true (altTypeOf w == some Digit.two) false)
        (altShifts (phase w == 1) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)).1
        (regOdo S oddO evenO (regsAt w).1 true) dsp ∧
    IsWeakDoublingAlt true FLatticePaper.Tiles.Side.hMinus (parentsAt w).odd.num (parentsAt w).odd.den true
        (FLatticePaper.Tiles.DoublingRespect.regWords true (regsAt w).1).1 (FLatticePaper.Tiles.DoublingRespect.regWords true (regsAt w).1).2
        (S.bdry (regsAt w).1 true) (altPartial S (regsAt w).1 true (altTypeOf w == some Digit.two) true)
        (altShifts (phase w == 1) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)).1
        (regOdo S oddO evenO (regsAt w).1 true) dsm ∧
    PlacedPiece (altOdd w) dsp
      (coeffOff (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
        (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) (altP0Coeff (phase w == 1) .dsP1Plus))
      (coeffAffine (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den
        (altP0Coeff (phase w == 1) .dsP1Plus)) ∧
    PlacedPiece (altOdd w) dsm
      (coeffOff (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
        (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) (altP0Coeff (phase w == 1) .dsP1Minus))
      (coeffAffine (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den
        (altP0Coeff (phase w == 1) .dsP1Minus)) ∧
    PlacedPiece (altOdd w) (regOdo S oddO evenO (regsAt w).2 false)
      (coeffOff (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
        (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) (altP0Coeff (phase w == 1) .q1Plus))
      (coeffAffine (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den
        (altP0Coeff (phase w == 1) .q1Plus)) ∧
    PlacedPiece (altOdd w) (regOdo S oddO evenO (regsAt w).2 false)
      (coeffOff (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
        (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) (altP0Coeff (phase w == 1) .q1Minus))
      (coeffAffine (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den
        (altP0Coeff (phase w == 1) .q1Minus)) ∧
    (match altTypeOf w with
      | none => True
      | some ty =>
        ParentPieceOk (altOdd w) (regOdo S altOdd altEven (regsAt w).2 false)
          (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)
          (texV2 (parentsAt w).even) (parentsAt w).odd.num (parentsAt w).odd.den
          (parentsAt w).even.num (parentsAt w).even.den (altQ1Coeff (phase w == 1) ty))

/-- The alternate even child `T̂(q_0)` of the word `w` (`eq:alt_decomp`, second line): the plain pieces `o_{p_1}^±` of the
odd register, the shifted doublings `ds(o)_{q_1}^±` of the even register (shift `S_q`), and the parent piece `ô(p_1)` of the
odd alternate register (when the type of `w` is not `three`). -/
def AltEvenNode (S : WeakData) (oddO evenO altOdd altEven : Word → PartialOdometer) (w : Word) : Prop :=
  ∃ dsp dsm : PartialOdometer,
    IsWeakDoublingAlt true (FLatticePaper.Tiles.DoublingRespect.doublingSide false (phase w == 1))
        (parentsAt w).odd.num (parentsAt w).odd.den true
        (FLatticePaper.Tiles.DoublingRespect.regWords false (regsAt w).2).1 (FLatticePaper.Tiles.DoublingRespect.regWords false (regsAt w).2).2
        (S.bdry (regsAt w).2 false) (altPartial S (regsAt w).2 false (altTypeOf w == some Digit.three) true)
        (altShifts (phase w == 1) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)).2
        (regOdo S oddO evenO (regsAt w).2 false) dsp ∧
    IsWeakDoublingAlt false (FLatticePaper.Tiles.DoublingRespect.doublingSide false (phase w == 1))
        (parentsAt w).odd.num (parentsAt w).odd.den true
        (FLatticePaper.Tiles.DoublingRespect.regWords false (regsAt w).2).1 (FLatticePaper.Tiles.DoublingRespect.regWords false (regsAt w).2).2
        (S.bdry (regsAt w).2 false) (altPartial S (regsAt w).2 false (altTypeOf w == some Digit.three) false)
        (altShifts (phase w == 1) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)).2
        (regOdo S oddO evenO (regsAt w).2 false) dsm ∧
    PlacedPiece (altEven w) dsp
      (coeffOff (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
        (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) (altQ0Coeff (phase w == 1) .dsQ1Plus))
      (coeffAffine (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den
        (altQ0Coeff (phase w == 1) .dsQ1Plus)) ∧
    PlacedPiece (altEven w) dsm
      (coeffOff (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
        (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) (altQ0Coeff (phase w == 1) .dsQ1Minus))
      (coeffAffine (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den
        (altQ0Coeff (phase w == 1) .dsQ1Minus)) ∧
    PlacedPiece (altEven w) (regOdo S oddO evenO (regsAt w).1 true)
      (coeffOff (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
        (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) (altQ0Coeff (phase w == 1) .p1Plus))
      (coeffAffine (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den
        (altQ0Coeff (phase w == 1) .p1Plus)) ∧
    PlacedPiece (altEven w) (regOdo S oddO evenO (regsAt w).1 true)
      (coeffOff (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
        (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even) (altQ0Coeff (phase w == 1) .p1Minus))
      (coeffAffine (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num (parentsAt w).even.den
        (altQ0Coeff (phase w == 1) .p1Minus)) ∧
    (match altTypeOf w with
      | none => True
      | some ty =>
        ParentPieceOk (altEven w) (regOdo S altOdd altEven (regsAt w).1 true)
          (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd) (texV1Even (parentsAt w).even)
          (texV2 (parentsAt w).even) (parentsAt w).odd.num (parentsAt w).odd.den
          (parentsAt w).even.num (parentsAt w).even.den (altP1Coeff (phase w == 1) ty))

/-- The lower-left anchors of the alternate tiles: `cHat w par` is `c(T̂)` of the alternate child of `w` (the lower-left vertex of
the tile, `def:alternate_tiles` and the corner convention of `lemma:alternate_tile_properties`). It is a parameter here: the
point-set construction of `SurgicalAltTiles` supplies it. -/
structure AltAnchors where
  cHat : Word → Bool → GInt

/-- The offset `s` of the odd alternate (`lemma:alternate_tile_properties` (3)(b), line 3606, operator answer): `s = 0` in the
even-first orientation (`W_1` even), and `s = -v_{q_1,1} + v_{p_1,2}` in the odd-first orientation (`W_1` odd), with the
parents of `w`. -/
def altOffsetS (w : Word) : GInt :=
  if phase w == 1 then
    (-(texV1Even (parentsAt w).even).1 + (texV2 (parentsAt w).odd).1,
      -(texV1Even (parentsAt w).even).2 + (texV2 (parentsAt w).odd).2)
  else (0, 0)

/-- The anchor of `rev(w_v)` of the odd alternate of `w`: `c(T̂) + s`. -/
def altRevVAnchor (anc : AltAnchors) (w : Word) : GInt :=
  anc.cHat w false + altOffsetS w

/-- The anchor of the forward horizontal word of the even alternate of `w`: `c(T̂)` (item (3a)). -/
def altFwdHAnchor (anc : AltAnchors) (w : Word) : GInt :=
  anc.cHat w true

/-- `o` respects the horizontal boundary word of an even alternate: the forward string at `c(T̂)` and the reversed string
somewhere (existential: the text gives no anchor for `rev(w_h)`, operator answer (B)). -/
def RespectsHalfH (cFwd : GInt) (wh : BinaryWord) (S : GInt → ℤ) : Prop :=
  RespectsTiles .horizontal false (hStringAt wh cFwd) S ∧
    ∃ c' : GInt, RespectsTiles .horizontal true (hRevStringAt wh.reverse c') S

/-- `o` respects the vertical boundary word of an odd alternate: the reversed string at the given anchor `cRev` (`c(T̂) + s`)
and the forward string somewhere (existential, operator answer (B)). -/
def RespectsHalfV (cRev : GInt) (wv : BinaryWord) (S : GInt → ℤ) : Prop :=
  RespectsTiles .vertical true (vRevStringAt wv.reverse cRev) S ∧
    ∃ c' : GInt, RespectsTiles .vertical false (vStringAt wv c') S

/-- The weak alternate odometer family (`def:weak_alternate_odometers`) over the standard family `oddO, evenO`: the standard
family is a weak standard family; each alternate odometer has the boundary tile of its word; a base word satisfies the base
condition; any other word has the alternate decompositions of its children; and the alternate odometer of an odd child
respects `w_v`, of an even child `w_h` (`lemma:weak_alternate_odometer_properties` (a)). -/
def IsWeakAltFamily (S : WeakData) (altBdry : Option Word → Bool → Finset GInt)
    (altBase : Word → PartialOdometer → PartialOdometer → Prop) (anc : AltAnchors)
    (oddO evenO altOdd altEven : Word → PartialOdometer) : Prop :=
  IsWeakStdFamily S oddO evenO ∧ ∀ w : Word,
    (altOdd w).dom = altBdry (some w) true ∧ (altEven w).dom = altBdry (some w) false ∧
    (FLatticePaper.Tiles.Standard.IsBase w → altBase w (altOdd w) (altEven w)) ∧
    (¬ FLatticePaper.Tiles.Standard.IsBase w →
      AltOddNode S oddO evenO altOdd altEven w ∧ AltEvenNode S oddO evenO altOdd altEven w) ∧
    RespectsHalfV (altRevVAnchor anc w) (FLatticePaper.Tiles.SiteStrings.vWordOf w false) (altOdd w).val ∧
    RespectsHalfH (altFwdHAnchor anc w) (FLatticePaper.Tiles.SiteStrings.hWordOf w true) (altEven w).val

/-- The alternate base condition of the base words (`prop:base_cases`, the alternate tiles and values): the same pairs of
tiles as `PaperBaseCond`, with the alternate tiles `paperStairAltTile` and the alternate values; the `N`-tiles are read at
`x + (0, 1)`. Membership is in the paper tiles (as sets). -/
def PaperAltBaseCond (w : Word) (O E : PartialOdometer) : Prop :=
  (w = [] →
    (∀ x : GInt, x ∈ O.dom ↔ x + (0, 1) ∈ paperNearStairAltTile 3) ∧
      (∀ x ∈ O.dom, O.val x = paperNearStairAltValue 3 (x + (0, 1))) ∧
    (∀ x : GInt, x ∈ E.dom ↔ x ∈ paperStairAltTile 3) ∧
      (∀ x ∈ E.dom, E.val x = paperStairAltValue 3 x)) ∧
  (∀ k : ℕ, 1 ≤ k → w = List.replicate k Digit.three →
    (∀ x : GInt, x ∈ O.dom ↔ x ∈ paperLadderAltTile (2 * (k : ℤ) + 2)) ∧
      (∀ x ∈ O.dom, O.val x = paperLadderAltValue (2 * (k : ℤ) + 2) x) ∧
    (∀ x : GInt, x ∈ E.dom ↔ x ∈ paperStairAltTile (2 * (k : ℤ) + 3)) ∧
      (∀ x ∈ E.dom, E.val x = paperStairAltValue (2 * (k : ℤ) + 3) x)) ∧
  (∀ k : ℕ, 1 ≤ k → w = List.replicate k Digit.two →
    (∀ x : GInt, x ∈ O.dom ↔ x + (0, 1) ∈ paperNearStairAltTile (2 * (k : ℤ) + 3)) ∧
      (∀ x ∈ O.dom, O.val x = paperNearStairAltValue (2 * (k : ℤ) + 3) (x + (0, 1))) ∧
    (∀ x : GInt, x ∈ E.dom ↔ x + (0, 1) ∈ paperNearLadderAltTile (2 * (k : ℤ) + 2)) ∧
      (∀ x ∈ E.dom, E.val x = paperNearLadderAltValue (2 * (k : ℤ) + 2) (x + (0, 1))))

/-- The weak alternate odometer family with the Section 6 standard base cases and the Section 6 alternate base cases. -/
def IsPaperWeakAltFamily (zeroO oneO : PartialOdometer) (bdry : Option Word → Bool → Finset Site)
    (partialT : Option Word → Bool → Bool → Finset Site) (altBdry : Option Word → Bool → Finset GInt)
    (anc : AltAnchors) (oddO evenO altOdd altEven : Word → PartialOdometer) : Prop :=
  IsWeakAltFamily (paperWeakData zeroO oneO bdry partialT) altBdry PaperAltBaseCond anc oddO evenO altOdd altEven

/-- (a) of `lemma:weak_alternate_odometer_properties` for the concrete instance, as the surgical text states it: `ô(n/d)`
respects `w_h(n/d)` if `n/d` is even and `w_v(n/d)` if it is odd. Even children are the even alternate `altEven w` (the word
`hWordOf w true`), odd children the odd alternate `altOdd w` (`hWordOf w false`). A projection of the family predicate. -/
theorem alt_respects_statement (zeroO oneO : PartialOdometer) (bdry : Option Word → Bool → Finset Site)
    (partialT : Option Word → Bool → Bool → Finset Site) (altBdry : Option Word → Bool → Finset GInt)
    (anc : AltAnchors) (oddO evenO altOdd altEven : Word → PartialOdometer)
    (h : IsPaperWeakAltFamily zeroO oneO bdry partialT altBdry anc oddO evenO altOdd altEven) (w : Word) :
    RespectsHalfV (altRevVAnchor anc w) (FLatticePaper.Tiles.SiteStrings.vWordOf w false) (altOdd w).val ∧
    RespectsHalfH (altFwdHAnchor anc w) (FLatticePaper.Tiles.SiteStrings.hWordOf w true) (altEven w).val :=
  ⟨(h.2 w).2.2.2.2.1, (h.2 w).2.2.2.2.2⟩

end FLatticePaper.Tiles.SurgicalAlt
