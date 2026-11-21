import FLatticePaper.Tiles.BoundaryStrings

/-! Zero-one odometers (paper Section 5.5, the first sentence of `lemma:stacked_zero_one_string`).

A domain is the list of sites of a tile translated to its position (membership is set membership). The tiles, the base
odometers, the slope `s(h)` and the offsets of a zero-one string are those of the paper. A family of odometers is
given by its tile letters, its tile positions `c(T_i)` and affine parameters `(a_i, b_i)`: the `i`-th odometer is
`x ↦ o_base(x − c_i) + a_i·x + b_i`. "Respects" (exact slope equations and the non-overlap rule) and "common
extension" (offset zero on overlaps) are Bool-valued checks, `ZOFamily.respectsB` and `ZOFamily.commonB`. The
existence statement is `ZeroOneFirstSentence`. The checks are decided on all words of length at most 6 in
`checks/ZeroOneOdometers.lean`; the statement for all words is not proved here. -/

namespace FLatticePaper.Tiles
open Finset

/-- The zero-tile `T_{0/1} = {0, i, 2i, 1, 1 + i, 1 + 2i}` (letter `p`). -/
def zeroTileSites : List Site := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]

/-- The one-tile `T_{1/1} = {0, i, 1, 1 + i}` (letter `q`). -/
def oneTileSites : List Site := [(0, 0), (0, 1), (1, 0), (1, 1)]

def tileSites : Letter → List Site
  | .p => zeroTileSites
  | .q => oneTileSites

/-- The zero-odometer: `-1` at `2i` and `1 + 2i`, `0` at the other sites of `T_{0/1}`. -/
def zeroOdometer (x : Site) : ℤ := if x = (0, 2) ∨ x = (1, 2) then -1 else 0

/-- The one-odometer: `-1` at `i`, `0` at the other sites of `T_{1/1}`. -/
def oneOdometer (x : Site) : ℤ := if x = (0, 1) then -1 else 0

def baseOdometer : Letter → Site → ℤ
  | .p => zeroOdometer
  | .q => oneOdometer

/-- The unit squares `{x, x + 1, x + i, x + 1 + i}` contained in `T`, by their lower-left corner `x`. -/
def unitSquares (T : List Site) : List Site :=
  T.filter fun x => decide (x + (1, 0) ∈ T ∧ x + (0, 1) ∈ T ∧ x + (1, 1) ∈ T)

/-- The slope `s(h)` of a partial odometer `h` on `T`: the average over the unit squares of `T` of
`(1/2)(h(x+1) − h(x) + h(x+1+i) − h(x+i)) + (i/2)(h(x+i) − h(x) + h(x+1+i) − h(x+1))`, as a pair of rationals
(real part, imaginary part). -/
def slopeOf (f : Site → ℤ) (T : List Site) : ℚ × ℚ :=
  let S := unitSquares T
  let re : ℚ := ((S.map fun x => ((f (x + (1, 0)) - f x + (f (x + (1, 1)) - f (x + (0, 1)))) : ℚ) / 2).sum)
  let im : ℚ := ((S.map fun x => ((f (x + (0, 1)) - f x + (f (x + (1, 1)) - f (x + (1, 0)))) : ℚ) / 2).sum)
  (re / (S.length : ℚ), im / (S.length : ℚ))

/-- The orientation of a zero-one string. -/
inductive Orientation
  | horizontal
  | vertical
  deriving DecidableEq, Repr

/-- The lower-left positions `c(T_1) = 0, c(T_2), …` of the tiles of a zero-one string on the letters `ls`. The
offsets are `eq:zero-one-bs` and `eq:zero-one-bs-vertical` (`rev = false`) or the reversed offsets
`eq:zero-one-bs-reversed` and `eq:zero-one-bs-reversed-vertical` (`rev = true`, read on consecutive pairs). -/
def stringPositions (o : Orientation) (rev : Bool) (ls : BinaryWord) : List Site :=
  let offsets : List Site :=
    if rev then
      List.zipWith (fun a l => match o with
        | .horizontal => zeroOneHorizontalReversedStep a l
        | .vertical => zeroOneVerticalReversedStep a l) ls ls.tail
    else
      ls.tail.map (fun l => match o with
        | .horizontal => zeroOneHorizontalStep l
        | .vertical => zeroOneVerticalStep l)
  List.scanl (· + ·) 0 offsets

/-- The exact slope equations `s(o_{i+1}) − s(o_i)` of `eq:zero-one-odometer_slopes-horizontal` and
`eq:zero-one-odometer_slopes-vert`, for the consecutive letters `(l, l')`. -/
def slopeDiff : Orientation → Letter → Letter → ℚ × ℚ
  | .horizontal, .p, .p => (0, 0)
  | .horizontal, .q, .q => (0, 0)
  | .horizontal, .p, .q => (-1 / 2, 0)
  | .horizontal, .q, .p => (1 / 2, 0)
  | .vertical, .p, .p => (0, -1)
  | .vertical, .q, .q => (1, -1)
  | .vertical, .p, .q => (1 / 2, -1)
  | .vertical, .q, .p => (1 / 2, -1)

/-- A family of zero-one odometers: tile letters, positions and the affine parameters of each odometer. -/
structure ZOFamily where
  n : ℕ
  letter : ℕ → Letter
  pos : ℕ → Site
  a : ℕ → Site
  b : ℕ → ℤ

/-- The `k`-th odometer of a family, on its domain. -/
def ZOFamily.odo (F : ZOFamily) (k : ℕ) (x : Site) : ℤ :=
  baseOdometer (F.letter k) (x - F.pos k) + (F.a k).1 * x.1 + (F.a k).2 * x.2 + F.b k

/-- The domain of the `k`-th odometer: the tile of its letter, translated to its position. -/
def ZOFamily.dom (F : ZOFamily) (k : ℕ) : List Site :=
  (tileSites (F.letter k)).map (· + F.pos k)

/-- Two sites are adjacent when they differ by a unit step. -/
def adjacentSites (x y : Site) : Bool := (x.1 - y.1).natAbs + (x.2 - y.2).natAbs == 1

/-- `Respects o F`: for consecutive tiles the slope equation holds exactly, and for consecutive tiles with
disjoint domains the adjacency rule holds (equal values in the horizontal case, the value difference `−1` in the
vertical case). -/
def ZOFamily.respectsB (o : Orientation) (F : ZOFamily) : Bool :=
  (List.range F.n).all fun k =>
    if k + 1 < F.n then
      decide (slopeOf (F.odo (k + 1)) (F.dom (k + 1)) - slopeOf (F.odo k) (F.dom k) =
          slopeDiff o (F.letter k) (F.letter (k + 1))) &&
        (if (F.dom k).all (fun x => decide (x ∉ F.dom (k + 1))) then
          (F.dom k).all fun x => (F.dom (k + 1)).all fun y =>
            if adjacentSites x y then
              match o with
              | .horizontal => F.odo k x == F.odo (k + 1) y
              | .vertical => F.odo (k + 1) y - F.odo k x == -1
            else true
        else true)
    else true

/-- `CommonExtension F`: the odometers agree (offset zero) on every overlap of two distinct domains. -/
def ZOFamily.commonB (F : ZOFamily) : Bool :=
  (List.range F.n).all fun k => (List.range F.n).all fun l =>
    if k = l then true
    else ((F.dom k).filter (fun x => decide (x ∈ F.dom l))).all fun x => F.odo k x == F.odo l x

/-- The affine parameters of the next odometer, from the previous tile, the next tile and the previous parameters.
The slope equation fixes the integer change of `a`; the constant `b` is fixed by the first overlap or adjacency. -/
def nextParams (o : Orientation) (lk l1 : Letter) (ck c1 ak : Site) (bk : ℤ) : Site × ℤ :=
  let δ : ℚ × ℚ := slopeDiff o lk l1 -
    (slopeOf (baseOdometer l1) (tileSites l1) - slopeOf (baseOdometer lk) (tileSites lk))
  let a1 : Site := (ak.1 + δ.1.num, ak.2 + δ.2.num)
  let odoPrev : Site → ℤ := fun x => baseOdometer lk (x - ck) + ak.1 * x.1 + ak.2 * x.2 + bk
  let tile (x : Site) : ℤ := baseOdometer l1 (x - c1) + a1.1 * x.1 + a1.2 * x.2
  let dk : List Site := (tileSites lk).map (· + ck)
  let d1 : List Site := (tileSites l1).map (· + c1)
  let overlap : List Site := dk.filter (fun x => decide (x ∈ d1))
  let adjacentPairs : List (Site × Site) :=
    dk.flatMap fun x => (d1.filter fun y => adjacentSites x y).map fun y => (x, y)
  let b1 : ℤ :=
    match overlap.head? with
    | some x => odoPrev x - tile x
    | none =>
      match adjacentPairs.head? with
      | some (x, y) =>
        match o with
        | .horizontal => odoPrev x - tile y
        | .vertical => odoPrev x - 1 - tile y
      | none => 0
  (a1, b1)

/-- The parameters of a whole string, from the letters and positions (the first odometer has parameters `(0, 0)`). -/
def buildAux (o : Orientation) : Letter → Site → Site → ℤ → List (Letter × Site) → List (Site × ℤ)
  | _, _, _, _, [] => []
  | lk, ck, ak, bk, (l1, c1) :: rest =>
    let p := nextParams o lk l1 ck c1 ak bk
    p :: buildAux o l1 c1 p.1 p.2 rest

def buildParams (o : Orientation) : List (Letter × Site) → List (Site × ℤ)
  | [] => []
  | (l0, c0) :: rest => (0, 0) :: buildAux o l0 c0 0 0 rest

/-- The family built for the zero-one string of the letters `w` (or of its reversal `w.reverse` when `rev`),
with the offsets of the (reversed) string. -/
def buildFamily (o : Orientation) (rev : Bool) (w : BinaryWord) : ZOFamily :=
  let L : BinaryWord := if rev then w.reverse else w
  let P : List Site := stringPositions o rev L
  let ab : List (Site × ℤ) := buildParams o (L.zip P)
  { n := L.length
    letter := fun k => L.getD k .p
    pos := fun k => P.getD k 0
    a := fun k => (ab.getD k (0, 0)).1
    b := fun k => (ab.getD k (0, 0)).2 }

/-- The first sentence of `lemma:stacked_zero_one_string` for one string: there is a family of zero-one odometers on
the tiles of the string (letters `w`, or `w.reverse` when `rev`, with the reversed offsets when `rev`), respecting
the string (slope equations and non-overlap rule) and with a common extension (offset zero on overlaps). -/
def ZeroOneFirstSentence (o : Orientation) (rev : Bool) (w : BinaryWord) : Prop :=
  ∃ F : ZOFamily,
    F.n = (if rev then w.reverse else w).length ∧
    (∀ k < F.n, F.letter k = (if rev then w.reverse else w).getD k .p) ∧
    (∀ k < F.n, F.pos k = (stringPositions o rev (if rev then w.reverse else w)).getD k 0) ∧
    F.respectsB o = true ∧ F.commonB = true

/-- The constructed family is a witness whenever its checks pass. -/
theorem zeroOneFirstSentence_of_checks (o : Orientation) (rev : Bool) (w : BinaryWord)
    (h1 : (buildFamily o rev w).respectsB o = true) (h2 : (buildFamily o rev w).commonB = true) :
    ZeroOneFirstSentence o rev w :=
  ⟨buildFamily o rev w, rfl, fun _ _ => rfl, fun _ _ => rfl, h1, h2⟩

/-- All binary words of length `m`. -/
def wordsOfLength : ℕ → List BinaryWord
  | 0 => [[]]
  | m + 1 => (wordsOfLength m).flatMap fun w => [Letter.p :: w, Letter.q :: w]

/-- The test: every word of length `1 ≤ |w| ≤ m` passes the checks for the string and for its reversal, in both
orientations. Returns the failing (orientation, reversed, word) triples. -/
def zeroOneFailures (m : ℕ) : List (Orientation × Bool × BinaryWord) :=
  [Orientation.horizontal, Orientation.vertical].flatMap fun o =>
    [false, true].flatMap fun rev =>
      ((List.range m).flatMap fun k => wordsOfLength (k + 1)).filterMap fun w =>
        if (buildFamily o rev w).respectsB o && (buildFamily o rev w).commonB then none
        else some (o, rev, w)

def zeroOneWordCount (m : ℕ) : ℕ := ((List.range m).flatMap fun k => wordsOfLength (k + 1)).length

end FLatticePaper.Tiles
