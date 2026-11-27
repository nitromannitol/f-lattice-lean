import FLatticePaper.Tiles.SurgicalOdometerStep
import FLatticePaper.Tiles.SurgicalCorners
import FLatticePaper.Tiles.StandardTiles
import FLatticePaper.Construction.OffsetTables
import FLatticePaper.Construction.PropBaseCases
import FLatticePaper.Construction.NearOneBaseCases
import FLatticePaper.Tiles.StackedMoreover
import FLatticePaper.Tiles.PartialBoundary
import FLatticePaper.Tiles.DoublingRespect
import FLatticePaper.Tiles.SiteStrings

/-! # The weak standard odometer family (surgical `def:weak_standard_odometers`, `def:standard_odometer_doubling`)

The recursion runs over the words of the Farey recursion, as the standard tiles do (`Tiles/StandardTiles.lean`). For a word
`w`, the odd child `T(p_0)` and the even child `T(q_0)` have odometers `oddO w` and `evenO w`. Their parents are the two
register tiles after reading `w` (`regsAt`, mirroring `tOdd_snoc_one` and the other register lemmas of `StandardTiles`):
the odd register holds the child `oddTile u` of the word `u` (or the initial tile `T_{0/1}`), the even register holds
`evenTile u` (or `T_{1/1}`). Their odometers are `regOdo`.

The decomposition of `o_{p_0}` (odd child) is `o_{p_1}^+ ∪ o_{p_1}^- ∪ d(o)_{q_1}^+ ∪ d(o)_{q_1}^-`, and that of `o_{q_0}`
(even child) is `d(o)_{p_1}^+ ∪ d(o)_{p_1}^- ∪ o_{q_1}^+ ∪ o_{q_1}^-` (`eq:std_odometer_decomposition`). The doubled pieces
are weak doublings (`IsWeakDoubling`). The offsets and affine factors are those of `IsStdStepP0W1Odd/Even` and
`IsStdStepQ0W1Odd/Even` (`SurgicalOdometerStep`, `SurgicalDict`), which take the Section 7 vectors and the parent fractions.

Everything the text leaves to the caller is a field of `WeakData`: the initial odometers `o_{0/1}`, `o_{1/1}`, the boundary
tiles `T^b` and the partial tiles `T^{h±/v±}` of each register (`bdry`, `partialT`), and the base predicate on base words.
The family predicate `IsWeakStdFamily` is a specification: its existence is the named hypothesis of the lemma, not proved here. -/

namespace FLatticePaper.Tiles.SurgicalWeak

open FLatticePaper.Farey
open FLatticePaper.Construction
open FLatticePaper.Tiles
open FLatticePaper.Tiles.SurgicalDict
open FLatticePaper.Tiles.Standard (stairF ladderF nstairN nladderN)

/-- The words whose child tiles sit in the odd and even registers after reading `pre` and then a letter. The pair
`(none, none)` stands for the initial tiles `T_{0/1}` (odd) and `T_{1/1}` (even), as in `StandardTiles.initState`. -/
def regStep (pre : Word) (r : Option Word × Option Word) : Digit → Option Word × Option Word
  | .one => (some pre, some pre)
  | .two => (some pre, r.2)
  | .three => (r.1, some pre)

/-- Reads the letters of a word after the prefix `pre`, on the register pair (mirrors `StandardTiles.runFrom`). -/
def regRun (pre : Word) : Word → Option Word × Option Word → Option Word × Option Word
  | [], r => r
  | d :: rest, r => regRun (pre ++ [d]) rest (regStep pre r d)

/-- The register pair after reading a word (mirrors `StandardTiles.stateAt`). -/
def regsAt (w : Word) : Option Word × Option Word := regRun [] w (none, none)

/-- The data the recursion reads but does not define. `zeroO`, `oneO` are the initial odometers `o_{0/1}`, `o_{1/1}`.
`bdry r odd` is the boundary tile `T^b` of the register `r` (`none` for the initial tiles), `partialT r odd side` the partial
tile `T^{h±/v±}` (`side = true` for `+`); in the doubling, the L-correction sign: `T^{L,∓}(p_0)` for `p`, `T^{L,±}(q_0)` for `q`. `base w o e` is the base condition of a base word `w` (`prop:base_cases`). -/
structure WeakData where
  zeroO : PartialOdometer
  oneO : PartialOdometer
  bdry : Option Word → Bool → Finset Site
  partialT : Option Word → Bool → Bool → Finset Site
  base : Word → PartialOdometer → PartialOdometer → Prop

/-- The odometer of a register: the initial odometer, or the odometer of the child of the register word. -/
def regOdo (S : WeakData) (oddO evenO : Word → PartialOdometer) : Option Word → Bool → PartialOdometer
  | none, true => S.zeroO
  | none, false => S.oneO
  | some u, true => oddO u
  | some u, false => evenO u

/-- A weak doubling of `o` on `T^b = Tb` with partial tile `Th` and shift `v` (`def:standard_odometer_doubling`,
`eq:doubled_odometer`): the doubled odometer `d` has domain `T^b ∪ (T^h + v)` and is `o ∪ o*`, with `o*` an odometer on
`T^h + v`. The respect relation of `o` and `o*` is a separate condition (the Section 5 respects, not part of this predicate). -/
def IsWeakDoubling (Tb Th : Finset Site) (v : Site) (o d : PartialOdometer) : Prop :=
  ∃ ostar : PartialOdometer, o.dom = Tb ∧ ostar.dom = Th.image (· + v) ∧
    d.dom = Tb ∪ Th.image (· + v) ∧
    (∀ x ∈ o.dom, d.val x = o.val x) ∧ (∀ x ∈ ostar.dom, d.val x = ostar.val x)

/-- The weak doubling with the data `ostar` of the second copy (the unfolded form of `IsWeakDoubling`). -/
def IsWeakDoublingOn (Tb Th : Finset Site) (v : Site) (o d ostar : PartialOdometer) : Prop :=
  o.dom = Tb ∧ ostar.dom = Th.image (· + v) ∧ d.dom = Tb ∪ Th.image (· + v) ∧
    (∀ x ∈ o.dom, d.val x = o.val x) ∧ (∀ x ∈ ostar.dom, d.val x = ostar.val x)

/-- The standard weak doubling (`def:standard_odometer_doubling`, manuscript f9cf1c2). The doubled odometer is `d = o ∪ o*`: the
given odometer `o` (domain `T^b`) is on the full copy and the odometer `o*` on the partial copy. With the partial tile on the second
copy (`firstPartial = false`), `d` is `IsWeakDoublingOn Tb Th v o d o*`: `o` at `0`, `o*` on `T^h + v`. With the partial tile on the
first copy (`firstPartial = true`, the text's "the partial tile is the first tile instead", `T^{d,p} = T^h ∪ (T^b + v)`), `o*` is on
`T^h` and the full copy `T^b + v` carries the translate `o_2` of `o` by `v` with the affine factor `a_{n/d,i}` (`IsTranslationOf`).
After restriction to the relevant side string of the partial tile (`DoublingRespect`), the first and the second copy respect the
tile translations, with the affine factor `a_{n/d,i}` (`i = false` for `v_{q,1}`, `i = true` for `v_{p,2}`). The side is
`doublingSide oddChild sideSign`, where `sideSign` already carries the flips of the text.

Correspondence (operator's measurements, S8_FIXES.md DS): the partial tile of `T^{d,p,±}(p_0)` is the L-correction `T^{L,∓}(p_0)`,
and that of `T^{d,p,±}(q_0)` is `T^{L,±}(q_0)`; the L-sign is the `side` argument of `partialT`. -/
def IsWeakDoublingStd (oddChild sideSign firstPartial : Bool) (n d : ℤ) (i : Bool) (wh wv : BinaryWord)
    (Tb Th : Finset Site) (v : Site) (o dd : PartialOdometer) : Prop :=
  ∃ ostar : PartialOdometer,
    if firstPartial then
      ∃ (o2 : PartialOdometer) (b : ℤ), o.dom = Tb ∧ IsTranslationOf o2 o v (offsetA n d i) b ∧
        IsWeakDoublingOn Th Tb v ostar dd o2 ∧
        FLatticePaper.Tiles.DoublingRespect.RespectsSideTranslation n d i wh wv
          (FLatticePaper.Tiles.DoublingRespect.doublingSide oddChild sideSign) v ostar o2
    else
      IsWeakDoublingOn Tb Th v o dd ostar ∧
        FLatticePaper.Tiles.DoublingRespect.RespectsSideTranslation n d i wh wv
          (FLatticePaper.Tiles.DoublingRespect.doublingSide oddChild sideSign) v o ostar

/-- The even-child decomposition with the offsets of `offsetQ0` (`eq:std_odometer_decomposition`, second line): the doubled
pieces `d(o)_{p_1}^±` at `p1DPlus`, `p1DMinus` and the plain pieces `o_{q_1}^±` at `q1Plus`, `q1Minus`. -/
def IsStdStepQ0 (odd : Bool) (vp1 vp2 vq1 vq2 : Site)
    (opz dpp dpm q1p q1m : PartialOdometer) (ap am aqp aqm : Site) : Prop :=
  PlacedPiece opz dpp (offsetQ0 odd vp1 vp2 vq1 vq2 .p1DPlus) ap ∧
  PlacedPiece opz dpm (offsetQ0 odd vp1 vp2 vq1 vq2 .p1DMinus) am ∧
  PlacedPiece opz q1p (offsetQ0 odd vp1 vp2 vq1 vq2 .q1Plus) aqp ∧
  PlacedPiece opz q1m (offsetQ0 odd vp1 vp2 vq1 vq2 .q1Minus) aqm

/-- The even child with `W_1` odd: the affine factors by the operator's rule (`pairAffine`). -/
def IsStdStepQ0W1Odd (vp1 vp2 vq1 vq2 : Site) (np dp nq dq : ℤ)
    (opz dpp dpm q1p q1m : PartialOdometer) : Prop :=
  IsStdStepQ0 true vp1 vp2 vq1 vq2 opz dpp dpm q1p q1m
    (pairAffine np dp 0 0) (pairAffine nq dq 1 1) (pairAffine np dp 1 0) (pairAffine np dp 0 2)

/-- The even child with `W_1` even: the affine factors by the operator's rule (`pairAffine`). -/
def IsStdStepQ0W1Even (vp1 vp2 vq1 vq2 : Site) (np dp nq dq : ℤ)
    (opz dpp dpm q1p q1m : PartialOdometer) : Prop :=
  IsStdStepQ0 false vp1 vp2 vq1 vq2 opz dpp dpm q1p q1m
    (pairAffine nq dq 1 0) (pairAffine nq dq 0 1) (pairAffine np dp 0 0) (pairAffine np dp 1 2)

/-! ### Step 1: the kept parts of the copies

Step 1 of `lemma:weak_standard_odometer_properties` deletes, from one of two overlapping copies of the same parent, their
overlap, except for the two copies of one doubled piece (surgical edition, notes S7_FIXES section 7). The nodes place each piece
on the kept part of its copies only: at the children corrected by Section 8 the overlaps of copies of the doubled parent in
different doubled pieces are not compatible (S7_FIXES 7.2, 0 of 216), so a placement on the whole copies cannot hold there. The
copies are those of `ChildGlue` (same order, same deletion rule, `keptPart` is `ChildGlue.keptSet`). -/

/-- A piece placed on a region `K` of the decomposed odometer: it is defined on `K` and equals the placed piece there, with the
affine factor `a` and a constant (`PlacedPiece` restricted to `K`). -/
def PlacedOn (parent child : PartialOdometer) (K : Set Site) (off a : Site) : Prop :=
  ∃ b : ℤ, (∀ x ∈ K, x ∈ parent.dom) ∧ ∀ x ∈ K, parent.val x = child.val (x - off) + (a.1 * x.1 + a.2 * x.2) + b

/-- The kept part of copy `i`: the copy minus the earlier copies of the same parent other than its doubled partner. -/
def keptPart (D : ℕ → Set Site) (flag : ℕ → Bool) (Dbl : ℕ → ℕ → Prop) (i : ℕ) : Set Site :=
  {z | z ∈ D i ∧ ¬ ∃ j, j < i ∧ flag j = flag i ∧ ¬ Dbl j i ∧ z ∈ D j}

/-- The affine factors of the pieces of the odd child (the tables of `IsStdStepP0W1Odd`, `IsStdStepP0W1Even`). -/
def p0AffTab (odd : Bool) (np dp nq dq : ℤ) : P0Piece → Site
  | .p1Plus => if odd then pairAffine nq dq 0 0 else pairAffine nq dq 2 0
  | .p1Minus => if odd then pairAffine nq dq 2 1 else pairAffine nq dq 0 1
  | .q1DPlus => if odd then pairAffine np dp 1 0 else pairAffine np dp 0 0
  | .q1DMinus => if odd then pairAffine np dp 0 1 else pairAffine np dp 1 1

/-- The affine factors of the pieces of the even child (the tables of `IsStdStepQ0W1Odd`, `IsStdStepQ0W1Even`). -/
def q0AffTab (odd : Bool) (np dp nq dq : ℤ) : Q0Piece → Site
  | .p1DPlus => if odd then pairAffine np dp 0 0 else pairAffine nq dq 1 0
  | .p1DMinus => if odd then pairAffine nq dq 1 1 else pairAffine nq dq 0 1
  | .q1Plus => if odd then pairAffine np dp 1 0 else pairAffine np dp 0 0
  | .q1Minus => if odd then pairAffine np dp 0 2 else pairAffine np dp 1 2

/-- The six copies of the odd child of `w` (the order of `ChildGlue`): the two plain copies of the odd register (domain `P`),
then the two copies of each doubled piece of the even register (boundary tile `Tb`, partial tiles `Thp`, `Thm`), the partial copy
being the first one of the `+` piece when `W_1` is odd and of the `-` piece when `W_1` is even (`IsWeakDoublingStd`). -/
def oddCopies (w : Word) (P Tb Thp Thm : Finset Site) : ℕ → Set Site := fun i =>
  let o := phase w == 1
  let vq1 := texV1Even (parentsAt w).even
  let off := offsetP0 o (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd) vq1 (texV2 (parentsAt w).even)
  match i with
  | 0 => ↑(P.image (· + off .p1Plus))
  | 1 => ↑(P.image (· + off .p1Minus))
  | 2 => ↑((if o then Thp else Tb).image (· + off .q1DPlus))
  | 3 => ↑((if o then Tb else Thp).image (· + (vq1 + off .q1DPlus)))
  | 4 => ↑((if o then Tb else Thm).image (· + off .q1DMinus))
  | 5 => ↑((if o then Thm else Tb).image (· + (vq1 + off .q1DMinus)))
  | _ => ∅

/-- The six copies of the even child of `w`: the two copies of each doubled piece of the odd register (boundary tile `Tb`,
partial tiles `Thp` on the second copy of `+` and `Thm` on the first copy of `-`), then the two plain copies of the even register
(domain `Q`). -/
def evenCopies (w : Word) (Tb Thp Thm Q : Finset Site) : ℕ → Set Site := fun i =>
  let vp2 := texV2 (parentsAt w).odd
  let off := offsetQ0 (phase w == 1) (texV1Odd (parentsAt w).odd) vp2 (texV1Even (parentsAt w).even)
    (texV2 (parentsAt w).even)
  match i with
  | 0 => ↑(Tb.image (· + off .p1DPlus))
  | 1 => ↑(Thp.image (· + (vp2 + off .p1DPlus)))
  | 2 => ↑(Thm.image (· + off .p1DMinus))
  | 3 => ↑(Tb.image (· + (vp2 + off .p1DMinus)))
  | 4 => ↑(Q.image (· + off .q1Plus))
  | 5 => ↑(Q.image (· + off .q1Minus))
  | _ => ∅

/-- The odd child `o_{p_0}` of the word `w` (`eq:std_odometer_decomposition`, first line). The parents are
`(parentsAt w).odd` (register `P`, plain pieces) and `(parentsAt w).even` (register `Q`, doubled pieces). The doubled
pieces `d(o)_{q_1}^±` are weak doublings of `Q` with shift `v_{q_1,1}` (`texV1Even`) on the partial tiles `T^{h±/v±}`.
`child` is the odometer of the child; the register odometers come from `pOdd`, `pEven` (in the joint family of Sections 7-8,
the tile odometers of the parent words, surgical 274ad18). Each piece is placed on the kept part of its copies (Step 1, `keptPart`):
the plain copy `T(p_1)^-` minus its overlap with `T(p_1)^+`, the doubled piece `d(o)_{q_1}^-` minus its overlaps with the copies
of `d(o)_{q_1}^+`; the offsets are those of `offsetP0` and the affine factors those of `IsStdStepP0W1Odd/Even`. -/
def OddNodeP (S : WeakData) (child : PartialOdometer) (pOdd pEven : Word → PartialOdometer) (w : Word) : Prop :=
  let K := keptPart (oddCopies w (regOdo S pOdd pEven (regsAt w).1 true).dom (S.bdry (regsAt w).2 false)
    (S.partialT (regsAt w).2 false true) (S.partialT (regsAt w).2 false false)) (fun i => decide (2 ≤ i))
    (fun i j => (i = 2 ∧ j = 3) ∨ (i = 4 ∧ j = 5))
  let off := offsetP0 (phase w == 1) (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
    (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
  let aff := p0AffTab (phase w == 1) (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
    (parentsAt w).even.den
  ∃ dqp dqm : PartialOdometer,
    IsWeakDoublingStd true true (phase w == 1) (parentsAt w).even.num (parentsAt w).even.den false
        (FLatticePaper.Tiles.DoublingRespect.regWords false (regsAt w).2).1 (FLatticePaper.Tiles.DoublingRespect.regWords false (regsAt w).2).2
        (S.bdry (regsAt w).2 false) (S.partialT (regsAt w).2 false true)
        (texV1Even (parentsAt w).even) (regOdo S pOdd pEven (regsAt w).2 false) dqp ∧
    IsWeakDoublingStd true false (!(phase w == 1)) (parentsAt w).even.num (parentsAt w).even.den false
        (FLatticePaper.Tiles.DoublingRespect.regWords false (regsAt w).2).1 (FLatticePaper.Tiles.DoublingRespect.regWords false (regsAt w).2).2
        (S.bdry (regsAt w).2 false) (S.partialT (regsAt w).2 false false)
        (texV1Even (parentsAt w).even) (regOdo S pOdd pEven (regsAt w).2 false) dqm ∧
    PlacedOn child (regOdo S pOdd pEven (regsAt w).1 true) (K 0) (off .p1Plus) (aff .p1Plus) ∧
    PlacedOn child (regOdo S pOdd pEven (regsAt w).1 true) (K 1) (off .p1Minus) (aff .p1Minus) ∧
    PlacedOn child dqp (K 2 ∪ K 3) (off .q1DPlus) (aff .q1DPlus) ∧
    PlacedOn child dqm (K 4 ∪ K 5) (off .q1DMinus) (aff .q1DMinus)

/-- The odd node of a family whose parents are its own odometers (the self-contained weak recursion). -/
def OddNode (S : WeakData) (oddO evenO : Word → PartialOdometer) (w : Word) : Prop :=
  OddNodeP S (oddO w) oddO evenO w

/-- The even child `o_{q_0}` of the word `w` (`eq:std_odometer_decomposition`, second line): the doubled pieces
`d(o)_{p_1}^±` (weak doublings of the odd register with shift `v_{p_1,2}`) and the plain pieces `o_{q_1}^±`.
The doubled `+` piece has its partial tile on the second copy with the side `v^+` for `W_1` even, `v^-` for `W_1` odd (the L-correction
`T^{L,-}(p_1)`); the doubled `-` piece has it on the first copy with the side `v^-` for `W_1` even, `v^+` for `W_1` odd (`T^{L,+}(p_1)`). `child` is the odometer of the child; the
register odometers come from `pOdd`, `pEven`, as in `OddNodeP`. Each piece is placed on the kept part of its copies (Step 1): the
doubled piece `d(o)_{p_1}^-` minus its overlaps with the copies of `d(o)_{p_1}^+`, the plain copy `T(q_1)^-` minus its overlap with
`T(q_1)^+`; offsets of `offsetQ0`, affine factors of `IsStdStepQ0W1Odd/Even`. -/
def EvenNodeP (S : WeakData) (child : PartialOdometer) (pOdd pEven : Word → PartialOdometer) (w : Word) : Prop :=
  let K := keptPart (evenCopies w (S.bdry (regsAt w).1 true) (S.partialT (regsAt w).1 true false)
    (S.partialT (regsAt w).1 true true) (regOdo S pOdd pEven (regsAt w).2 false).dom) (fun i => decide (4 ≤ i))
    (fun i j => (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3))
  let off := offsetQ0 (phase w == 1) (texV1Odd (parentsAt w).odd) (texV2 (parentsAt w).odd)
    (texV1Even (parentsAt w).even) (texV2 (parentsAt w).even)
  let aff := q0AffTab (phase w == 1) (parentsAt w).odd.num (parentsAt w).odd.den (parentsAt w).even.num
    (parentsAt w).even.den
  ∃ dpp dpm : PartialOdometer,
    IsWeakDoublingStd false (!(phase w == 1)) false (parentsAt w).odd.num (parentsAt w).odd.den true
        (FLatticePaper.Tiles.DoublingRespect.regWords true (regsAt w).1).1 (FLatticePaper.Tiles.DoublingRespect.regWords true (regsAt w).1).2
        (S.bdry (regsAt w).1 true) (S.partialT (regsAt w).1 true false)
        (texV2 (parentsAt w).odd) (regOdo S pOdd pEven (regsAt w).1 true) dpp ∧
    IsWeakDoublingStd false (phase w == 1) true (parentsAt w).odd.num (parentsAt w).odd.den true
        (FLatticePaper.Tiles.DoublingRespect.regWords true (regsAt w).1).1 (FLatticePaper.Tiles.DoublingRespect.regWords true (regsAt w).1).2
        (S.bdry (regsAt w).1 true) (S.partialT (regsAt w).1 true true)
        (texV2 (parentsAt w).odd) (regOdo S pOdd pEven (regsAt w).1 true) dpm ∧
    PlacedOn child dpp (K 0 ∪ K 1) (off .p1DPlus) (aff .p1DPlus) ∧
    PlacedOn child dpm (K 2 ∪ K 3) (off .p1DMinus) (aff .p1DMinus) ∧
    PlacedOn child (regOdo S pOdd pEven (regsAt w).2 false) (K 4) (off .q1Plus) (aff .q1Plus) ∧
    PlacedOn child (regOdo S pOdd pEven (regsAt w).2 false) (K 5) (off .q1Minus) (aff .q1Minus)

/-- The even node of a family whose parents are its own odometers (the self-contained weak recursion). -/
def EvenNode (S : WeakData) (oddO evenO : Word → PartialOdometer) (w : Word) : Prop :=
  EvenNodeP S (evenO w) oddO evenO w

/-- `o` respects `(w_h, w_v)` (`def:tile_boundary_strings`, with `c(T) = 0`, the normalisation of the standard tiles, and
the anchors of `anchoredStrings`): the domain contains the four boundary strings, and the restrictions of `o` to the forward
horizontal and reversed vertical strings at `c(T)`, and to the reversed horizontal and forward vertical strings at their
anchors, respect them (`RespectsTiles`, the surgical table `surgicalSlopeDiff`). -/
def RespectsAnchored (T : Finset Site) (wh wv : BinaryWord) (S : GInt → ℤ) : Prop :=
  InsideTile (↑T : Set GInt) (hStringAt wh 0 ++ hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0)) ++
      vRevStringAt wv.reverse 0 ++ vStringAt wv (lastPosOf (hStringAt wh 0))) ∧
  RespectsTiles .horizontal false (hStringAt wh 0) S ∧
  RespectsTiles .horizontal true (hRevStringAt wh.reverse (lastPosOf (vRevStringAt wv.reverse 0))) S ∧
  RespectsTiles .vertical true (vRevStringAt wv.reverse 0) S ∧
  RespectsTiles .vertical false (vStringAt wv (lastPosOf (hStringAt wh 0))) S

/-- The weak standard odometer family (`def:weak_standard_odometers`): for every word, the odometers of the two children
have the boundary tiles `T^b` as domains; a base word satisfies the base condition `S.base`; any other word has the
standard decompositions of its two children (`OddNode`, `EvenNode`) from its register odometers. -/
def IsWeakStdFamily (S : WeakData) (oddO evenO : Word → PartialOdometer) : Prop :=
  ∀ w : Word,
    (oddO w).dom = S.bdry (some w) true ∧ (evenO w).dom = S.bdry (some w) false ∧
    (FLatticePaper.Tiles.Standard.IsBase w → S.base w (oddO w) (evenO w)) ∧
    (¬ FLatticePaper.Tiles.Standard.IsBase w → OddNode S oddO evenO w ∧ EvenNode S oddO evenO w) ∧
    RespectsAnchored (oddO w).dom (FLatticePaper.Tiles.SiteStrings.hWordOf w false)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w false) (oddO w).val ∧
    RespectsAnchored (evenO w).dom (FLatticePaper.Tiles.SiteStrings.hWordOf w true)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w true) (evenO w).val

/-! ### The Section 6 instance (`prop:base_cases`)

For the base words of the Farey recursion, the children are the base tiles of `StandardTiles.childTiles`: `[]` gives
`(nstairN 3, stairF 3)`, `3^k` gives `(ladderF (2k+2), stairF (2k+3))` and `2^k` gives `(nstairN (2k+3), nladderN (2k+2))`.
Their vertex sets are the paper tiles (`stairF d = paperStairTile d`, `ladderF d = paperLadderTile d`, and the `N`-tiles are
the near-one tiles shifted by `(0, -1)`, so the values are read at `x + (0, 1)`). The base odometers are the Section 6
values there, with no additive constant. -/

/-- The concrete base condition of the base words (`prop:base_cases`, the odometers of the standard base tiles). -/
def PaperBaseCond (w : Word) (O E : PartialOdometer) : Prop :=
  (w = [] →
    O.dom = nstairN 3 ∧ (∀ x ∈ O.dom, O.val x = paperNearStairValue 3 (x + (0, 1))) ∧
    E.dom = stairF 3 ∧ (∀ x ∈ E.dom, E.val x = paperStairValue 3 x)) ∧
  (∀ k : ℕ, 1 ≤ k → w = List.replicate k Digit.three →
    O.dom = ladderF (2 * (k : ℤ) + 2) ∧
      (∀ x ∈ O.dom, O.val x = paperLadderValue (2 * (k : ℤ) + 2) x) ∧
    E.dom = stairF (2 * (k : ℤ) + 3) ∧
      (∀ x ∈ E.dom, E.val x = paperStairValue (2 * (k : ℤ) + 3) x)) ∧
  (∀ k : ℕ, 1 ≤ k → w = List.replicate k Digit.two →
    O.dom = nstairN (2 * (k : ℤ) + 3) ∧
      (∀ x ∈ O.dom, O.val x = paperNearStairValue (2 * (k : ℤ) + 3) (x + (0, 1))) ∧
    E.dom = nladderN (2 * (k : ℤ) + 2) ∧
      (∀ x ∈ E.dom, E.val x = paperNearLadderValue (2 * (k : ℤ) + 2) (x + (0, 1))))

/-- The weak standard data with the Section 6 base condition. -/
def paperWeakData (zeroO oneO : PartialOdometer) (bdry : Option Word → Bool → Finset Site)
    (partialT : Option Word → Bool → Bool → Finset Site) : WeakData :=
  { zeroO := zeroO, oneO := oneO, bdry := bdry, partialT := partialT, base := PaperBaseCond }

/-- The weak standard odometer family with the Section 6 base cases. -/
def IsPaperWeakStdFamily (zeroO oneO : PartialOdometer) (bdry : Option Word → Bool → Finset Site)
    (partialT : Option Word → Bool → Bool → Finset Site) (oddO evenO : Word → PartialOdometer) : Prop :=
  IsWeakStdFamily (paperWeakData zeroO oneO bdry partialT) oddO evenO

/-- (a) for the concrete instance (`lemma:weak_standard_odometer_properties` (a)): in every weak standard family with the
Section 6 base cases, the odometer of each word respects its horizontal and vertical boundary words at the anchors
(`RespectsAnchored`), for the odd child (`hWordOf w false`, `vWordOf w false`) and the even child (`hWordOf w true`,
`vWordOf w true`). The statement is a projection of the family predicate. -/
theorem paper_respects_statement (zeroO oneO : PartialOdometer) (bdry : Option Word → Bool → Finset Site)
    (partialT : Option Word → Bool → Bool → Finset Site) (oddO evenO : Word → PartialOdometer)
    (h : IsPaperWeakStdFamily zeroO oneO bdry partialT oddO evenO) (w : Word) :
    RespectsAnchored (oddO w).dom (FLatticePaper.Tiles.SiteStrings.hWordOf w false)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w false) (oddO w).val ∧
    RespectsAnchored (evenO w).dom (FLatticePaper.Tiles.SiteStrings.hWordOf w true)
        (FLatticePaper.Tiles.SiteStrings.vWordOf w true) (evenO w).val :=
  ⟨(h w).2.2.2.2.1, (h w).2.2.2.2.2⟩

/-! ### Named hypotheses

Each is a statement that another worker proves. They are used by name and are not proved here. -/

/-- (a) of `lemma:weak_standard_odometer_properties`, through the Section 5 Moreover. Source: `HorizontalMoreover` and
`VerticalMoreover` (Tiles/StackedMoreover.lean, w2; surgical Section 5). Stated as w2 states it, for all words. -/
def SectionFiveMoreoverHyp : Prop :=
  ∀ w : BinaryWord, HorizontalMoreover w ∧ VerticalMoreover w

/-- Base existence, reciprocal stair family. Source: `prop_base_cases_reciprocal_stair`, Construction/PropBaseCases.lean line
115 (w1; the odometer item). -/
def BaseReciprocalStairHyp (k : ℕ) : Prop :=
  UniqueRecurrentExtension (Fraction.mk 1 (2 * (k : ℤ) + 3)) (paperStairTile (2 * (k : ℤ) + 3))
    (paperStairValue (2 * (k : ℤ) + 3))

/-- Base existence, doubled stair (ladder) family. Source: `prop_base_cases_doubled_stair`, PropBaseCases.lean line 133 (w1). -/
def BaseDoubledStairHyp (m : ℕ) : Prop :=
  UniqueRecurrentExtension (Fraction.mk 1 (2 * (m : ℤ) + 4)) (paperLadderTile (2 * (m : ℤ) + 4))
    (paperLadderValue (2 * (m : ℤ) + 4))

/-- Base existence, near-one stair family. Source: `prop_base_cases_near_stair`, PropBaseCases.lean lines 158-160 (w1). -/
def BaseNearStairHyp (k : ℕ) : Prop :=
  UniqueNearOneExtension (Fraction.rotate (⟨1, 2 * (k : ℤ) + 3⟩ : Fraction))
    (paperNearStairTile (2 * (k : ℤ) + 3)) (paperNearStairValue (2 * (k : ℤ) + 3))

/-- Base existence, near-one doubled stair (near ladder) family. Source: `prop_base_cases_near_doubled_stair`, PropBaseCases.lean
lines 185-186 (w1). -/
def BaseNearDoubledStairHyp (m : ℕ) : Prop :=
  UniqueNearOneExtension (Fraction.rotate (⟨1, 2 * (m : ℤ) + 4⟩ : Fraction))
    (paperNearLadderTile (2 * (m : ℤ) + 4)) (paperNearLadderValue (2 * (m : ℤ) + 4))

/-- The base existence of all four families (`prop:base_cases`, w1). -/
def BaseFamiliesHyp : Prop :=
  (∀ k : ℕ, BaseReciprocalStairHyp k) ∧ (∀ m : ℕ, BaseDoubledStairHyp m) ∧
    (∀ k : ℕ, BaseNearStairHyp k) ∧ (∀ m : ℕ, BaseNearDoubledStairHyp m)

/-! ### The target of (c) (not proved; held until w2's stacked common extension is on main)

`lemma:weak_standard_odometer_properties` (c): lattice adjacent weak standard odometers are compatible. The proof in the text
copies the proof of `lemma:standard_tile_properties` (c) and needs the common extension on the stacked boundary strings
(`lemma:stacked_zero_one_string`, w2's `CrossCommon`). It is stated here as a target only. -/

/-- The target of (c): two lattice adjacent odometers (`LatticeAdjacent`) are compatible (`Compatible`). -/
def LatticeCompatibleTarget (n d : ℤ) (i : Bool) (c c' vi : Site) (o o' : PartialOdometer) : Prop :=
  LatticeAdjacent n d i c c' vi o o' → Compatible o o'

end FLatticePaper.Tiles.SurgicalWeak
