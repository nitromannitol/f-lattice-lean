import FLatticePaper.Tiles.StandardTiles
import FLatticePaper.Tiles.IncrementCounts

/-! Task 51, step 1 (the fix of Q9): the four marked strings of a standard tile, as sets of sites.

The standard tiles are the Lean definitions `Standard.oddTile w` and `Standard.evenTile w` (the literal six-copy supports; the
Python `std_odd`, `std_even` of `scripts/alt_tiles.py` are the same recursion, `std_children` against `childTiles`). The zero-one
words are the quads of `IncrementCounts`: `hWordOf w par` is the forward horizontal word (`childP` for the odd tile, `childQ` for
the even one), and `vWordOf w par` is the reversed-vertical word, the child word of the swapped word with the letters exchanged.

The strings are read as in the Python check `check_standard_strings.py` (`family`): a letter at a tile of the string sits at the
origin reached by the offsets of `dxdy`; a horizontal `qq` pair is enlarged by the two tips `(-1,1)`, `(1,-1)` of the second tile.
The four marked strings of the tile with lower-left vertex `c` are: the forward horizontal string of `w_h` at `c`; the reversed
vertical string of `rev w_v` at `c - (1,1)`; and their images under the half-turn of the site set `(x,y) ↦ (rx - x, ry - y)` with
`rx = min x + max x`, `ry = min y + max y`. The two clauses are: the marked sites lie in the tile, and the inner boundary (sites
with a unit neighbour outside the tile) is covered. -/

namespace FLatticePaper.Tiles.SiteStrings

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard

/-- The sites of a zero-one tile of letter `l` relative to its origin: `p` is the `2 × 3` rectangle, `q` the `2 × 2` one, and an
enlarged `q` (a `qq` pair in a horizontal string) has the two tips `(-1, 1)` and `(1, -1)`. -/
def baseSites : Letter → Bool → List (ℤ × ℤ)
  | .p, _ => [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]
  | .q, false => [(0, 0), (0, 1), (1, 0), (1, 1)]
  | .q, true => [(0, 0), (0, 1), (1, 0), (1, 1), (-1, 1), (1, -1)]

/-- The origin of the first tile of a string: the lower-left `(0,0)` for a forward string, and `(1,1)` (vertical) or `(1,-2)`
(horizontal) for a reversed one. -/
def startPos (vert rev : Bool) : ℤ × ℤ :=
  if rev then (if vert then (1, 1) else (1, -2)) else (0, 0)

/-- The step from a tile of letter `prev` to a tile of letter `l` (the offsets of the string). Horizontal: `x` advances by `1`,
or by `2` when the letter read is a `p`; `y` advances by one for a `q`. Vertical: `x` retreats by one for a `p`; `y` advances by one
for a `p` and by two for a `q`. In a reversed string the letter read is the previous one. -/
def dxdy (vert rev : Bool) (prev l : Letter) : ℤ × ℤ :=
  if vert then
    ((if (if rev then prev else l) = .p then -1 else 0), if l = .p then 1 else 2)
  else
    ((if (if rev then prev else l) = .p then 2 else 1), if l = .q then 1 else 0)

/-- The origins of the tiles of a string, with the letter and the enlargement flag of each tile. The enlargement of a horizontal
tile is the `qq` pair: the previous and the current letter are both `q`. -/
def origins (vert rev : Bool) : Option Letter → ℤ × ℤ → List Letter → List ((ℤ × ℤ) × Letter × Bool)
  | _, _, [] => []
  | none, pos, l :: ls => (pos, l, false) :: origins vert rev (some l) pos ls
  | some pr, pos, l :: ls =>
      let pos' : ℤ × ℤ := (pos.1 + (dxdy vert rev pr l).1, pos.2 + (dxdy vert rev pr l).2)
      (pos', l, !vert && pr == .q && l == .q) :: origins vert rev (some l) pos' ls

/-- The sites of a string of letters, with the origins of its tiles. -/
def stringSites (vert rev : Bool) (ls : List Letter) : List (ℤ × ℤ) :=
  (origins vert rev none (startPos vert rev) ls).flatMap fun o =>
    (baseSites o.2.1 o.2.2).map fun b => (o.1.1 + b.1, o.1.2 + b.2)

/-- The origin of the last tile of a string (the `c(last)` of the check). -/
def lastOrigin (vert rev : Bool) (ls : List Letter) : Option (ℤ × ℤ) :=
  ((origins vert rev none (startPos vert rev) ls).getLast?).map (·.1)

/-- The lower-left vertex `c(T)` of a finite site set: the least imaginary part, then the least real part. -/
def lowLeft (T : Finset (ℤ × ℤ)) : ℤ × ℤ :=
  match (T.image fun z => toLex (z.2, z.1)).min with
  | some l => ((ofLex l).2, (ofLex l).1)
  | none => (0, 0)

/-- The least real part of a finite site set. -/
def minX (T : Finset (ℤ × ℤ)) : ℤ := ((T.image Prod.fst).min).getD 0

/-- The greatest real part of a finite site set. -/
def maxX (T : Finset (ℤ × ℤ)) : ℤ := ((T.image Prod.fst).max).getD 0

/-- The least imaginary part of a finite site set. -/
def minY (T : Finset (ℤ × ℤ)) : ℤ := ((T.image Prod.snd).min).getD 0

/-- The greatest imaginary part of a finite site set. -/
def maxY (T : Finset (ℤ × ℤ)) : ℤ := ((T.image Prod.snd).max).getD 0

/-- The half-turn constant `(rx, ry)` of a site set: `rx = min x + max x`, `ry = min y + max y`. -/
def halfTurnCentre (T : Finset (ℤ × ℤ)) : ℤ × ℤ := (minX T + maxX T, minY T + maxY T)

/-- The half-turn of a site set: `z ↦ (rx - z.1, ry - z.2)`. -/
def halfTurn (T : Finset (ℤ × ℤ)) (z : ℤ × ℤ) : ℤ × ℤ :=
  ((halfTurnCentre T).1 - z.1, (halfTurnCentre T).2 - z.2)

/-- The unit neighbours of a site. -/
def unitNeighbours (z : ℤ × ℤ) : List (ℤ × ℤ) :=
  [(z.1 + 1, z.2), (z.1 - 1, z.2), (z.1, z.2 + 1), (z.1, z.2 - 1)]

/-- The inner boundary `∂⁻T`: the sites of `T` with a unit neighbour outside `T`. -/
def InnerBoundary (T : Finset (ℤ × ℤ)) (z : ℤ × ℤ) : Prop :=
  z ∈ T ∧ ∃ e ∈ unitNeighbours z, e ∉ T

instance (T : Finset (ℤ × ℤ)) (z : ℤ × ℤ) : Decidable (InnerBoundary T z) := by
  unfold InnerBoundary
  infer_instance

/-- The four marked strings of a tile `T` with the zero-one words `wh` (forward horizontal) and `vw` (the reversed vertical word
`vw` before reversal): the forward horizontal string at `c(T)`, the reversed vertical string at `c(T) - (1,1)`, and their half-turn
images (the reversed horizontal string and the second vertical string). -/
def markedSites (T : Finset (ℤ × ℤ)) (wh vw : List Letter) : List (ℤ × ℤ) :=
  let c := lowLeft T
  let Sh := (stringSites false false wh).map fun z => (z.1 + c.1, z.2 + c.2)
  let Sv := (stringSites true true vw.reverse).map fun z => (z.1 + c.1 - 1, z.2 + c.2 - 1)
  Sh ++ Sv ++ Sh.map (halfTurn T) ++ Sv.map (halfTurn T)

/-- **The Q9 four-string predicate** on a finite site set `T`: clause 1, the marked sites lie in `T`; clause 2, the inner boundary
`∂⁻T` is covered by the marked sites. -/
def FourStrings (T : Finset (ℤ × ℤ)) (wh vw : List Letter) : Prop :=
  (∀ z ∈ markedSites T wh vw, z ∈ T) ∧ (∀ z ∈ T, InnerBoundary T z → z ∈ markedSites T wh vw)

instance (T : Finset (ℤ × ℤ)) (wh vw : List Letter) : Decidable (FourStrings T wh vw) := by
  unfold FourStrings
  infer_instance

/-- The reflected consistency of the reading: the reversed horizontal string (with its enlarged `qq` pairs) at the reflected origin
is the half-turn image of the forward horizontal string. -/
def ReflectedOK (T : Finset (ℤ × ℤ)) (wh : List Letter) : Prop :=
  let c := lowLeft T
  let rx := (halfTurnCentre T).1
  let ry := (halfTurnCentre T).2
  match lastOrigin false false wh with
  | none => True
  | some last =>
    let rev := (stringSites false true wh.reverse).map fun z =>
      (z.1 + rx - c.1 - last.1 - 2, z.2 + ry - c.2 - last.2)
    let Sh := (stringSites false false wh).map fun z => (z.1 + c.1, z.2 + c.2)
    (∀ z ∈ rev, z ∈ Sh.map (halfTurn T)) ∧ (∀ z ∈ Sh.map (halfTurn T), z ∈ rev)

instance (T : Finset (ℤ × ℤ)) (wh : List Letter) : Decidable (ReflectedOK T wh) := by
  unfold ReflectedOK
  split <;> infer_instance

/-! ### The words of the tile -/

/-- The forward horizontal word of the tile of `w` with parity `par` (`false`: odd, `childP`; `true`: even, `childQ`). -/
def hWordOf (w : Word) (par : Bool) : List Letter :=
  if par then (quadAt [] w).childQ else (quadAt [] w).childP

/-- The reversed vertical word of the tile of `w` with parity `par`: the other child of the swapped word, with the letters
exchanged (the `translate(pq→qp)` of the check). -/
def vWordOf (w : Word) (par : Bool) : List Letter :=
  (if par then (quadAt [] (Standard.swapW w)).childP else (quadAt [] (Standard.swapW w)).childQ).map swapLetter

/-- The standard tile of `w` with parity `par` (`false`: odd, `true`: even). -/
def tileOf (w : Word) (par : Bool) : Finset (ℤ × ℤ) := if par then evenTile w else oddTile w

/-- The Q9 four-string predicate for the standard tile of `w` with parity `par`. -/
def StandardFourStrings (w : Word) (par : Bool) : Prop :=
  FourStrings (tileOf w par) (hWordOf w par) (vWordOf w par)

/-- The reflected consistency for the standard tile of `w` with parity `par`. -/
def StandardReflectedOK (w : Word) (par : Bool) : Prop :=
  ReflectedOK (tileOf w par) (hWordOf w par)

/-- The standard tile of `w` with parity `par`, as the reading is decided on it. -/
instance (w : Word) (par : Bool) : Decidable (StandardFourStrings w par) := by
  unfold StandardFourStrings
  infer_instance

/-- All digit words of length `n`. -/
def digitWords : ℕ → List Word
  | 0 => [[]]
  | n + 1 => [Digit.one, Digit.two, Digit.three].flatMap fun d => (digitWords n).map (d :: ·)

end FLatticePaper.Tiles.SiteStrings
