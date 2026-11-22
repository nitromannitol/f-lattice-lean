import FLatticePaper.Tiles.FourWalks
import FLatticePaper.Tiles.StandardBaseWords

/-! `StandardBoundaryWord` from the bottom seams (TeX 2723, steps 2 and 3).

For a word `u`, the boundary-word statement of the odd (resp. even) standard tile is the four-walk criterion
`FourWalks.isBoundaryFrom_boundaryWordOf` applied to the bottom word `oddBottom u` and the right word `oddRight u`.
The structure `BottomSeamOdd u` (resp. `BottomSeamEven u`) collects the seam facts about the cell tile of the child, the
named inputs of the induction:

* `low`: the lower-left vertex of the cell tile is `(0, 0)` (normalisation);
* `symm`: the tile is symmetric under `e ↦ z - e`, `z = Σ bottom + Σ right` (from `rot_rot_oddTile`, numerically the
  same centre on 353 words);
* `sub`: the bottom staircase of the copies and the right staircase are boundary edges of the child (TeX 3005(d), the
  bottom part is the numerically verified `ChildBottomChain` seam; the right part is its rotation);
* `cover`, `nodup`: the four walks cover the boundary, each edge once (the seam completeness of 3005(d)).

The base words are proved unconditionally (`StandardBaseWords.lean`). -/

namespace FLatticePaper.Tiles.BottomSeam

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardClause
open FLatticePaper.Tiles.BoundaryWalks FLatticePaper.Tiles.FourWalks FLatticePaper.Tiles.StandardBaseWords

/-- The seam facts of the odd child of `u`. -/
structure BottomSeamOdd (u : Word) : Prop where
  low : IsLowerLeft (cellTileOf (oddTile u)) (0, 0)
  symm : ∀ e ∈ (cellTileOf (oddTile u)).boundaryEdges,
    halfE (F2Word.sum (oddBottom u) + F2Word.sum (oddRight u)) e ∈ (cellTileOf (oddTile u)).boundaryEdges
  sub : ∀ e ∈ edgesFrom 0 (oddBottom u) ++ edgesFrom (F2Word.sum (oddBottom u)) (oddRight u),
    e ∈ (cellTileOf (oddTile u)).boundaryEdges
  cover : ∀ e ∈ (cellTileOf (oddTile u)).boundaryEdges,
    e ∈ edgesFrom 0 (boundaryWordOf (oddBottom u) (oddRight u))
  nodup : (edgesFrom 0 (boundaryWordOf (oddBottom u) (oddRight u))).Nodup

/-- The seam facts of the even child of `u`. -/
structure BottomSeamEven (u : Word) : Prop where
  low : IsLowerLeft (cellTileOf (evenTile u)) (0, 0)
  symm : ∀ e ∈ (cellTileOf (evenTile u)).boundaryEdges,
    halfE (F2Word.sum (evenBottom u) + F2Word.sum (evenRight u)) e ∈ (cellTileOf (evenTile u)).boundaryEdges
  sub : ∀ e ∈ edgesFrom 0 (evenBottom u) ++ edgesFrom (F2Word.sum (evenBottom u)) (evenRight u),
    e ∈ (cellTileOf (evenTile u)).boundaryEdges
  cover : ∀ e ∈ (cellTileOf (evenTile u)).boundaryEdges,
    e ∈ edgesFrom 0 (boundaryWordOf (evenBottom u) (evenRight u))
  nodup : (edgesFrom 0 (boundaryWordOf (evenBottom u) (evenRight u))).Nodup

theorem standardBoundaryOdd_of_seam (u : Word) (h : BottomSeamOdd u) : StandardBoundaryOdd u := by
  unfold StandardBoundaryOdd
  rw [isBoundaryWordAt_iff]
  exact ⟨h.low, isBoundaryFrom_boundaryWordOf _ _ _ h.symm h.sub h.cover h.nodup⟩

theorem standardBoundaryEven_of_seam (u : Word) (h : BottomSeamEven u) : StandardBoundaryEven u := by
  unfold StandardBoundaryEven
  rw [isBoundaryWordAt_iff]
  exact ⟨h.low, isBoundaryFrom_boundaryWordOf _ _ _ h.symm h.sub h.cover h.nodup⟩

/-- `StandardBoundaryWord u` for a non-base word, from its two seams. -/
theorem standardBoundaryWord_of_seams (u : Word) (hO : BottomSeamOdd u) (hE : BottomSeamEven u) :
    StandardBoundaryWord u :=
  ⟨standardBoundaryOdd_of_seam u hO, standardBoundaryEven_of_seam u hE⟩

/-- Every base word has the standard boundary word (proved in `StandardBaseWords.lean`). -/
theorem standardBoundaryWord_of_isBase (u : Word) (hb : IsBase u) : StandardBoundaryWord u := by
  rcases hb with rfl | h3 | h2
  · exact standardBoundaryWord_nil
  · have hu : u = List.replicate u.length Digit.three := List.eq_replicate_iff.mpr ⟨rfl, h3⟩
    cases hl : u.length with
    | zero =>
      have : u = [] := List.eq_nil_of_length_eq_zero hl
      subst this
      exact standardBoundaryWord_nil
    | succ m =>
      rw [hl] at hu
      rw [hu]
      exact standardBoundaryWord_three m
  · have hu : u = List.replicate u.length Digit.two := List.eq_replicate_iff.mpr ⟨rfl, h2⟩
    cases hl : u.length with
    | zero =>
      have : u = [] := List.eq_nil_of_length_eq_zero hl
      subst this
      exact standardBoundaryWord_nil
    | succ m =>
      rw [hl] at hu
      rw [hu]
      exact standardBoundaryWord_two m

end FLatticePaper.Tiles.BottomSeam
