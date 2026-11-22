import FLatticePaper.Tiles.StandardTiles

/-! # Alternate tiles (`def:alternate_tiles`), PROVISIONAL reading (task 33)

`def:alternate_tiles` of the paper attaches an alternate tile pair `(T̂(p_0), T̂(q_0))` to each word, by the decomposition
`eq:alt_decomp` into standard tiles of the parents `(p_1, q_1)` and the alternate tiles of the parents, with the placements of
`eq:alt_offsets_w1_odd` and `eq:alt_offsets_w1_even` and the alternate placements of the type of the last letter.
The doubling vectors are `eq:alt_doubled`.

The reading below follows the TeX as printed, in the registers of `StandardTiles.lean` (the alternate registers hold the
alternate tiles of the parents, starting from `(T_{0/1}, T_{1/1})`).

PROVISIONAL points (numerically tested, `scripts/alt_checks.py`, `scripts/alt_report.txt`):
* The alternate piece `T̂(q_1)` (resp. `T̂(p_1)`) is omitted where the TeX writes `-`: for the odd child of an odd-first word
  of type 2, of an even-first word of type 2; for the even child, of type 3. The constructor's `seventhAlternateJet` places
  it in some of these cases too (not followed here).
* The base alternate tiles of `prop:base_cases` are translated to their lowest cell at the origin (`altStairN`, `altLadderN`,
  `altNearStairN`, `altNearLadderN`); the normalising vectors are the ones that make the lowest cell the origin. The stair and
  ladder families are not normalised by the same rule in the paper's chart (see the report).
* The origin of an alternate tile is the origin of its listed offsets (the TeX's `c(T̂)` exception is the piece at offset `0`).

Results (words up to length 4): the standard tiles satisfy the checks of `StandardTiles.lean`; the alternate tiles are
edge-connected and cover the lattice vertices under `L'`, but are not row-convex, not always hole-free, and the rotation
identity `R(T̂(p_0)) = T̂(q_0 of the swapped word) + tF` holds only for some words (see `checks/AlternateTiles.lean`). -/

namespace FLatticePaper.Tiles.Alternate

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles.Standard

/-! ### Base alternate tiles of `prop:base_cases` (the alternate rows), as finite sets of cells

The raw sets are those of `lemma:basecase_3k_even_alt` and `lemma:basecase_3k_odd_alt` (reciprocal) and of
`lemma:basecase_2k_odd_alt` and `lemma:basecase_2k_even_alt` (near-one); the boxes contain their supports for `d ≥ 3`. -/

/-- `paperStairAltTile d` (`lemma:basecase_3k_even_alt`), `d` odd `≥ 3`. -/
def altStairRaw (d : ℤ) : Tile :=
  (Finset.Icc (-d - 3) (2 * d + 3) ×ˢ Finset.Icc (-3) (3 * d + 3)).filter fun x : Site =>
    (x.1 = 1 - d ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∨ (x.1 = 3 ∧ d ≤ x.2 ∧ x.2 ≤ d + 1) ∨
    (x.1 + x.2 = 2 ∧ 0 < x.2 ∧ x.2 < d) ∨
    (1 - d ≤ x.1 ∧ x.1 ≤ 0 ∧ x.2 = -1) ∨ (4 - d ≤ x.1 ∧ x.1 ≤ 3 ∧ x.2 = d + 1) ∨
    (4 - 2 * d ≤ x.1 ∧ x.1 ≤ d ∧ 0 ≤ x.2 ∧ x.2 ≤ d ∧ -d + 2 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ d + 2)

/-- `paperLadderAltTile d` (`lemma:basecase_3k_odd_alt`), `d` even `≥ 4`. -/
def altLadderRaw (d : ℤ) : Tile :=
  (Finset.Icc (-d - 3) (2 * d + 3) ×ˢ Finset.Icc (-3) (3 * d + 3)).filter fun x : Site =>
    ((x = (-1, -1) ∨ x = (d, d + 2)) ∨ (x.1 + x.2 = d ∧ 0 < x.1 ∧ x.1 < d - 1) ∨
      (1 - d ≤ x.1 ∧ x.1 ≤ 2 * d - 2 ∧ -1 ≤ x.2 ∧ x.2 ≤ d + 2 ∧ -1 ≤ x.1 + x.2 ∧ x.1 + x.2 ≤ 2 * d + 1)) ∧
    ¬ ((d ≤ x.1 ∧ -1 ≤ x.2 ∧ x.2 ≤ 0) ∨ (x.1 ≤ -1 ∧ d + 1 ≤ x.2 ∧ x.2 ≤ d + 2))

/-- `paperNearStairAltTile d` (`lemma:basecase_2k_odd_alt`), `d` odd `≥ 3`, before normalisation. -/
def altNearStairRaw (d : ℤ) : Tile :=
  (Finset.Icc (-d - 3) (2 * d + 3) ×ˢ Finset.Icc (-3) (3 * d + 3)).filter fun x : Site =>
    ((-1 ≤ x.1 ∧ x.1 ≤ 0 ∧ x.2 = 2 * d) ∨ (d ≤ x.1 ∧ x.1 ≤ d + 1 ∧ x.2 = d - 2) ∨
      (x.2 - x.1 = d - 1 ∧ 0 < x.1 ∧ x.1 < d) ∨
      (x.1 = -1 ∧ d + 1 ≤ x.2 ∧ x.2 ≤ 2 * d) ∨ (x.1 = d + 1 ∧ d - 2 ≤ x.2 ∧ x.2 ≤ 2 * d - 3) ∨
      (0 ≤ x.1 ∧ x.1 ≤ d ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 3 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d - 1))

/-- `paperNearLadderAltTile d` (`lemma:basecase_2k_even_alt`), `d` even `≥ 4`, before normalisation. -/
def altNearLadderRaw (d : ℤ) : Tile :=
  (Finset.Icc (-d - 3) (2 * d + 3) ×ˢ Finset.Icc (-3) (3 * d + 3)).filter fun x : Site =>
    ((x = (-2, 2 * d) ∨ x = (d + 1, d - 1)) ∨ (x.2 - x.1 = d ∧ 0 < x.1 ∧ x.1 < d - 1) ∨
      (-2 ≤ x.1 ∧ x.1 ≤ d + 1 ∧ 1 ≤ x.2 ∧ x.2 ≤ 3 * d - 2 ∧ -1 ≤ x.2 - x.1 ∧ x.2 - x.1 ≤ 2 * d + 1)) ∧
    ¬ ((x.1 ≤ -1 ∧ x.2 ≤ d - 1) ∨ (d ≤ x.1 ∧ 2 * d ≤ x.2))

/-- The base alternate stair `T̂_{1/d}` of `prop:base_cases`, translated to lowest cell at the origin (PROVISIONAL). -/
def altStairN (d : ℤ) : Tile := shift (altStairRaw d) (d - 1, 1)

/-- The base alternate ladder `T̂_{1/d}`, translated to lowest cell at the origin (PROVISIONAL). -/
def altLadderN (d : ℤ) : Tile := shift (altLadderRaw d) (1, 1)

/-- The base alternate near-one stair, translated to lowest cell at the origin (PROVISIONAL). -/
def altNearStairN (d : ℤ) : Tile := shift (altNearStairRaw d) (0, -1)

/-- The base alternate near-one ladder, translated to lowest cell at the origin (PROVISIONAL). -/
def altNearLadderN (d : ℤ) : Tile := shift (altNearLadderRaw d) (0, -1)

/-- The alternate tiles of the children of a base word (`prop:base_cases`): the empty word, `3^k` and `2^k`
(`k ≥ 1`), with the children of `childTiles`. -/
def altBase (w : Word) : Tile × Tile :=
  if w = [] then (altNearStairN 3, altStairN 3)
  else if w = List.replicate w.length Digit.three then
    (altLadderN (2 * (w.length : ℤ) + 2), altStairN (2 * (w.length : ℤ) + 3))
  else
    (altNearStairN (2 * (w.length : ℤ) + 3), altNearLadderN (2 * (w.length : ℤ) + 2))

/-! ### The alternate decomposition (`eq:alt_decomp`, `eq:alt_doubled`, `eq:alt_offsets_w1_odd/even`) -/

/-- The last letter of a word (its type). -/
def lastDigit (w : Word) : Digit := w.getLast?.getD Digit.one

/-- The alternate tiles of the children of a non-base word `w`, with `p = p_1` the odd parent, `q = q_1` the even parent,
`tO = T(p_1)`, `tE = T(q_1)`, `aO = T̂(p_1)`, `aE = T̂(q_1)`, and `flag` the parity of the number of `1`s of `w`
(`flag = true` is `W_1` odd). The doubling vectors are `eq:alt_doubled`. PROVISIONAL, see the module note. -/
def altPair (flag : Bool) (typ : Digit) (tO tE aO aE : Tile) (p q : Fraction) : Tile × Tile :=
  let V1o := texV1Odd p
  let V2p := texV2 p
  let V1e := texV1Even q
  let V2q := texV2 q
  let Sp : Site := if flag then -V1e + V2p else V1e + V2p
  let Sq : Site := if flag then V1e + V2p else -V1e + V2p
  let dsP : Site → Tile := fun o => shift tO o ∪ shift tO (o + Sp)
  let dsQ : Site → Tile := fun o => shift tE o ∪ shift tE (o + Sq)
  if flag then
    (shift tE V1o ∪ shift tE (2 • V2p - V1e) ∪ dsP 0 ∪ dsP (V1e + V2q) ∪
        (if typ = Digit.one ∨ typ = Digit.three then shift aE (V2p + V1o - V1e) else ∅),
      dsQ V1o ∪ dsQ V2p ∪ shift tO 0 ∪ shift tO (V2p + V2q + 2 • V1e) ∪
        (if typ = Digit.one then shift aO (V2p + V1e)
          else if typ = Digit.two then shift aO (2 • V1e + V2q) else ∅))
  else
    (shift tE 0 ∪ shift tE (V1o + 2 • V2p + V1e) ∪ dsP V1e ∪ dsP V2q ∪
        (if typ = Digit.one ∨ typ = Digit.three then shift aE (V1e + V2p) else ∅),
      dsQ 0 ∪ dsQ (V1o + V2p) ∪ shift tO V1e ∪ shift tO (V2p + V2q - V1e) ∪
        (if typ = Digit.one then shift aO (V2p + V1o - V1e)
          else if typ = Digit.two then shift aO V2q else ∅))

/-! ### Registers and the alternate tiles of a word -/

/-- The state of a word: the standard state, and the alternate tiles of the two parents. -/
structure AState where
  std : TState
  aOdd : Tile
  aEven : Tile

/-- The alternate tiles of the children of the prefix `pre` from the state `s` of `pre`. -/
def altChildren (pre : Word) (s : AState) : Tile × Tile :=
  if IsBase pre then altBase pre
  else altPair (phase pre == 1) (lastDigit pre) s.std.tOdd s.std.tEven s.aOdd s.aEven
    s.std.par.odd s.std.par.even

/-- One letter: the standard registers advance as in `stepState`; the alternate registers receive the alternate children
of the prefix, in the same places as the standard ones. -/
def altStep (pre : Word) (s : AState) (d : Digit) : AState :=
  let c := altChildren pre s
  let std' := stepState pre s.std d
  match d with
  | .one => ⟨std', c.1, c.2⟩
  | .two => ⟨std', c.1, s.aEven⟩
  | .three => ⟨std', s.aOdd, c.2⟩

/-- Reads the letters of a word after the prefix `pre`. -/
def altRun (pre : Word) : Word → AState → AState
  | [], s => s
  | d :: rest, s => altRun (pre ++ [d]) rest (altStep pre s d)

/-- The state after reading a word: the parents of the word, their standard tiles and their alternate tiles. -/
def altState (w : Word) : AState :=
  altRun [] w ⟨initState, zeroTile, oneTile⟩

/-- The alternate odd child `T̂(p_0)` of the parent pair of `w`. -/
def altOddTile (w : Word) : Tile := (altChildren w (altState w)).1

/-- The alternate even child `T̂(q_0)` of the parent pair of `w`. -/
def altEvenTile (w : Word) : Tile := (altChildren w (altState w)).2

/-! ### The alternate state carries the Farey registers of every word -/

theorem altStep_std (pre : Word) (s : AState) (d : Digit) : (altStep pre s d).std = stepState pre s.std d := by
  cases d <;> rfl

theorem altRun_std (pre rest : Word) (s : AState) :
    (altRun pre rest s).std = runFrom pre rest s.std := by
  induction rest generalizing pre s with
  | nil => rfl
  | cons d rest ih =>
    rw [altRun, runFrom, ih, altStep_std]

/-- For every word, the standard part of the alternate state is the standard state of the word. -/
theorem altState_std (w : Word) : (altState w).std = stateAt w := by
  unfold altState stateAt
  rw [altRun_std]

/-- For every word, the parent pair of the alternate state is the parent pair `parentsAt w` of the Farey recursion. -/
theorem altState_par (w : Word) : (altState w).std.par = parentsAt w := by
  rw [altState_std, stateAt_par]

end FLatticePaper.Tiles.Alternate
