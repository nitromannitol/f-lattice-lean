import FLatticePaper.Tiles.AlmostTilingAssembly
import FLatticePaper.Tiles.StandardTiles

/-! Clause (a) of `lemma:standard_tile_properties` (`paper/farey_recursion.tex` 3005), for every word, derived from named
inputs by `almost_square_tiling`.

The cell tile of a vertex set `P` is `cellTileOf P`: the cells (lower-left corners) whose four corners lie in `P`
(the convention of the repo's `stairCells`, `ladderCells`; `R2` in the notes). The standard tile of a word is the cell
tile of `oddTile w` or `evenTile w` (`StandardTiles.lean`).

The inputs of the structure `StandardInputs` are the statements that are not yet proved for all words:
* `bdOdd`, `bdEven`: the boundary word of the cell tile from its lower-left vertex `(0,0)` is `w1 * w2 * hat(rev w1) *
  hat(rev w2)` with the bottom-edge words `W1`, `V1` and the right-edge words `W2`, `V2` (the boundary-word input,
  `StandardBoundaryWord`, numerically verified on the cell tiles of words of length at most six);
* `sumOdd`, `sumEven`: the sums `Sigma w1 + i` and `Sigma w2 - 1` are the lattice vectors (texV1Odd, texV2 for the odd
  tile, texV1Even, texV2 for the even tile), from w3's recursion;
* `admOdd`, `admEven`: admissibility of `w1` and `-i w2` (w3);
* `simpleOdd`, `simpleEven`: the cell tile is simple (`IsSimpleTile`);
* `packOdd`, `packEven`: the packing hypothesis of `almost_square_tiling`, stated, not proved (`NoFirstCrossing`,
  `NoFarAdjacency`). -/

namespace FLatticePaper.Tiles.StandardClause

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard

/-- The cell tile of a vertex set: the cells (lower-left corners) whose four corners lie in the set. -/
def cellTileOf (P : Finset Site) : CellTile := P.filter fun a => cellCorners a ⊆ P

/-- The fraction of the odd tile of `w` (the odd child of the parent pair at `w`). -/
def fracOdd (w : Word) : Fraction := (parentsAt w).current .odd

/-- The fraction of the even tile of `w`. -/
def fracEven (w : Word) : Fraction := (parentsAt w).current .even

/-- The named inputs of clause (a), for every word. -/
structure StandardInputs where
  W1 : Word → F2Word
  W2 : Word → F2Word
  V1 : Word → F2Word
  V2 : Word → F2Word
  bdOdd : ∀ w, IsBoundaryWordAt (cellTileOf (oddTile w)) (0, 0) (boundaryWordOf (W1 w) (W2 w))
  bdEven : ∀ w, IsBoundaryWordAt (cellTileOf (evenTile w)) (0, 0) (boundaryWordOf (V1 w) (V2 w))
  sumOdd : ∀ w, almostV₁ (W1 w) = texV1Odd (fracOdd w) ∧ almostV₂ (W2 w) = texV2 (fracOdd w)
  sumEven : ∀ w, almostV₁ (V1 w) = texV1Even (fracEven w) ∧ almostV₂ (V2 w) = texV2 (fracEven w)
  admOdd : ∀ w, Admissible (W1 w) ∧ Admissible ((W2 w).map Unit4.mulNegI)
  admEven : ∀ w, Admissible (V1 w) ∧ Admissible ((V2 w).map Unit4.mulNegI)
  simpleOdd : ∀ w, IsSimpleTile (cellTileOf (oddTile w))
  simpleEven : ∀ w, IsSimpleTile (cellTileOf (evenTile w))
  packOdd : ∀ w, NoFirstCrossing (cellTileOf (oddTile w)) (almostV₁ (W1 w)) (almostV₂ (W2 w)) ∧
    NoFarAdjacency (cellTileOf (oddTile w)) (almostV₁ (W1 w)) (almostV₂ (W2 w))
  packEven : ∀ w, NoFirstCrossing (cellTileOf (evenTile w)) (almostV₁ (V1 w)) (almostV₂ (V2 w)) ∧
    NoFarAdjacency (cellTileOf (evenTile w)) (almostV₁ (V1 w)) (almostV₂ (V2 w))

/-- Clause (a) for the odd tile of `w`: the cell tile generates the `(texV1Odd f, texV2 f)`-regular almost tiling, with
`f = fracOdd w`. -/
theorem clauseA_odd (I : StandardInputs) (w : Word) :
    IsRegularAlmostTiling (cellTileOf (oddTile w)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) := by
  obtain ⟨hA, -⟩ := almost_square_tiling (I.simpleOdd w) (I.bdOdd w) (I.admOdd w).1 (I.admOdd w).2
    (I.packOdd w).1 (I.packOdd w).2
  rw [(I.sumOdd w).1, (I.sumOdd w).2] at hA
  exact hA

/-- Clause (a) for the even tile of `w`. -/
theorem clauseA_even (I : StandardInputs) (w : Word) :
    IsRegularAlmostTiling (cellTileOf (evenTile w)) (texV1Even (fracEven w)) (texV2 (fracEven w)) := by
  obtain ⟨hA, -⟩ := almost_square_tiling (I.simpleEven w) (I.bdEven w) (I.admEven w).1 (I.admEven w).2
    (I.packEven w).1 (I.packEven w).2
  rw [(I.sumEven w).1, (I.sumEven w).2] at hA
  exact hA

/-- The edge-sharing clause of `almost_square_tiling` for the odd tile of `w`, with the same lattice. -/
theorem edgeClauseA_odd (I : StandardInputs) (w : Word) :
    EdgeSharingClause (cellTileOf (oddTile w)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) := by
  obtain ⟨-, hE⟩ := almost_square_tiling (I.simpleOdd w) (I.bdOdd w) (I.admOdd w).1 (I.admOdd w).2
    (I.packOdd w).1 (I.packOdd w).2
  rw [(I.sumOdd w).1, (I.sumOdd w).2] at hE
  exact hE

end FLatticePaper.Tiles.StandardClause
