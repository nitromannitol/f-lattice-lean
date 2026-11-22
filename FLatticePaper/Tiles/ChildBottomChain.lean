import FLatticePaper.Tiles.BoundaryWalks
import FLatticePaper.Tiles.StandardBoundary

/-! The bottom staircase of a standard child tile (TeX lemma 2723, step 2).

The bottom edge of the child is the concatenation of the bottom edges of its lower copies, joined by single `i` steps:
`w_{t+1} = w_t i v_t i v_t` for the odd child and `v_t i w_t` for the even child (the recursion of `BottomEdges.lean`).
Geometrically, the copies sit at the offsets `0`, `texV1Odd p`, `texV1Odd p + texV1Even q` (`oddChildB`), and the
`i` joins are the steps between consecutive copies.

Proved here: the walk algebra of such a chain, and the offsets from the sum theorems of `StandardBoundary.lean`.
Named inputs (not proved here): the seam fact F1 (`BottomSeam`), that the copies' walks and the joins are boundary
edges of the child's cell tile (TeX `lemma:standard_tile_properties` (d); checked numerically on 2184 tiles). -/

namespace FLatticePaper.Tiles.ChildBottomChain

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardClause

theorem vec_i : Unit4.vec Unit4.i = gI := rfl

/-- A walk through a join `u i v`: the walk of `u`, then the step `i`, then the walk of `v`. -/
theorem edgesFrom_join (o : GInt) (u v : F2Word) :
    edgesFrom o (u ++ Unit4.i :: v) =
      edgesFrom o u ++ (o + F2Word.sum u, o + F2Word.sum u + gI) :: edgesFrom (o + F2Word.sum u + gI) v := by
  rw [edgesFrom_append]
  congr 1

/-- The odd bottom staircase `w i v i v`: three copies joined by two `i` steps. -/
theorem odd_chain (o : GInt) (B1 B2 B3 : F2Word) :
    edgesFrom o (B1 ++ Unit4.i :: (B2 ++ Unit4.i :: B3)) =
      edgesFrom o B1 ++ (o + F2Word.sum B1, o + F2Word.sum B1 + gI) ::
        (edgesFrom (o + F2Word.sum B1 + gI) B2 ++
          (o + F2Word.sum B1 + gI + F2Word.sum B2, o + F2Word.sum B1 + gI + F2Word.sum B2 + gI) ::
            edgesFrom (o + F2Word.sum B1 + gI + F2Word.sum B2 + gI) B3) := by
  rw [edgesFrom_join, edgesFrom_join]

/-- The even bottom staircase `v i w`: two copies joined by one `i` step. -/
theorem even_chain (o : GInt) (B1 B2 : F2Word) :
    edgesFrom o (B1 ++ Unit4.i :: B2) =
      edgesFrom o B1 ++ (o + F2Word.sum B1, o + F2Word.sum B1 + gI) :: edgesFrom (o + F2Word.sum B1 + gI) B2 := by
  rw [edgesFrom_join]

/-- The offset of the second odd copy is the bottom sum of the odd parent plus the join `i`
(`texV1Odd p = Σ w + i`, from `sum_oddBottom`). -/
theorem oddOffset_eq (u : Word) : texV1Odd (fracOdd u) = F2Word.sum (oddBottom u) + gI := by
  rw [← sum_oddBottom]
  rfl

/-- The offset between the two `v`-copies of the odd child is the even bottom sum plus the join `i`. -/
theorem evenOffset_eq (u : Word) : texV1Even (fracEven u) = F2Word.sum (evenBottom u) + gI := by
  rw [← sum_evenBottom]
  rfl

/-- The seam fact F1 (named input): the walk of a bottom staircase starting at `o` is a boundary walk of the child's
cell tile `C`, i.e. each of its directed edges is a boundary edge of `C`. Numerically checked on the 2184 tiles of
words of length 1 to 6 (copies at the offsets of `oddChildB`/`evenChildB`, joins as boundary edges). -/
structure BottomSeam (C : CellTile) (o : GInt) (w : F2Word) : Prop where
  edges_mem : ∀ e ∈ edgesFrom o w, e ∈ C.boundaryEdges

/-- Under F1, the odd bottom staircase is a boundary walk of the child: every edge of the concatenation of the three
copy walks and the two joins is a boundary edge of the child. -/
theorem odd_chain_mem (C : CellTile) (o : GInt) (B1 B2 B3 : F2Word)
    (h : BottomSeam C o (B1 ++ Unit4.i :: (B2 ++ Unit4.i :: B3))) :
    ∀ e ∈ edgesFrom o (B1 ++ Unit4.i :: (B2 ++ Unit4.i :: B3)), e ∈ C.boundaryEdges :=
  h.edges_mem

end FLatticePaper.Tiles.ChildBottomChain
