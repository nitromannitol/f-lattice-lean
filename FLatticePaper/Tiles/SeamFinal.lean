import FLatticePaper.Tiles.RightSub
import FLatticePaper.Tiles.BottomSeam
import FLatticePaper.Tiles.StandardBaseWords

/-! `StandardBoundaryWord` from the two named seam facts of each word (TeX 3005(d) and lemma 2723, step 2).

Derived (no input): the lower-left vertex (`OriginCell.lowerLeft_origin`), the half-turn symmetry (`SeamSymm.symm_odd`,
`symm_even`), and the right edge (`RightSub.right_sub_odd`, `right_sub_even`, from the bottom copy of the swapped word).

Named inputs, per word `v`:
* `BottomCopyOdd v`, `BottomCopyEven v`: the bottom walk of the odd (resp. even) child of `v` from `(0, 0)` is a walk along the
  boundary of its cell tile. This is the copy-level seam (the copies' bottom walks and the `i` joins, `ChildBottomChain`).
* `CoverNodupOdd v`, `CoverNodupEven v`: the four walks `E₁ ++ E₂ ++ halfE E₁ ++ halfE E₂` cover the boundary of the cell
  tile, and list each boundary edge once. This is the seam completeness of 3005(d). -/

namespace FLatticePaper.Tiles.SeamFinal

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.BoundaryWalks
open FLatticePaper.Tiles.FourWalks FLatticePaper.Tiles.SeamSymm FLatticePaper.Tiles.RightSub
open FLatticePaper.Tiles.OriginCell FLatticePaper.Tiles.StandardBaseWords FLatticePaper.Tiles.BottomSeam

/-- Named input: the bottom walk of the odd child of `v` lies on the boundary of its cell tile. -/
def BottomCopyOdd (v : Word) : Prop :=
  ∀ e ∈ edgesFrom 0 (oddBottom v), e ∈ CellTile.boundaryEdges (cellTileOf (oddTile v))

/-- Named input: the bottom walk of the even child of `v` lies on the boundary of its cell tile. -/
def BottomCopyEven (v : Word) : Prop :=
  ∀ e ∈ edgesFrom 0 (evenBottom v), e ∈ CellTile.boundaryEdges (cellTileOf (evenTile v))

/-- Named input: the four walks of the odd child of `v` cover its boundary, each edge once. -/
structure CoverNodupOdd (v : Word) : Prop where
  cover : ∀ e ∈ CellTile.boundaryEdges (cellTileOf (oddTile v)),
    e ∈ edgesFrom 0 (boundaryWordOf (oddBottom v) (oddRight v))
  nodup : (edgesFrom 0 (boundaryWordOf (oddBottom v) (oddRight v))).Nodup

/-- Named input: the four walks of the even child of `v` cover its boundary, each edge once. -/
structure CoverNodupEven (v : Word) : Prop where
  cover : ∀ e ∈ CellTile.boundaryEdges (cellTileOf (evenTile v)),
    e ∈ edgesFrom 0 (boundaryWordOf (evenBottom v) (evenRight v))
  nodup : (edgesFrom 0 (boundaryWordOf (evenBottom v) (evenRight v))).Nodup

theorem standardBoundaryOdd_of_named (v : Word) (hB : BottomCopyOdd v) (hBs : BottomCopyEven (swapW v))
    (hC : CoverNodupOdd v) : StandardBoundaryOdd v := by
  unfold StandardBoundaryOdd
  rw [isBoundaryWordAt_iff]
  refine ⟨(lowerLeft_origin v).1, ?_⟩
  refine isBoundaryFrom_boundaryWordOf _ _ _ (symm_odd v) ?_ hC.cover hC.nodup
  intro e he
  rw [List.mem_append] at he
  rcases he with h | h
  · exact hB e h
  · exact right_sub_odd v hBs e h

theorem standardBoundaryEven_of_named (v : Word) (hB : BottomCopyEven v) (hBs : BottomCopyOdd (swapW v))
    (hC : CoverNodupEven v) : StandardBoundaryEven v := by
  unfold StandardBoundaryEven
  rw [isBoundaryWordAt_iff]
  refine ⟨(lowerLeft_origin v).2, ?_⟩
  refine isBoundaryFrom_boundaryWordOf _ _ _ (symm_even v) ?_ hC.cover hC.nodup
  intro e he
  rw [List.mem_append] at he
  rcases he with h | h
  · exact hB e h
  · exact right_sub_even v hBs e h

/-- `StandardBoundaryWord` for a word, from its named seam facts (the word and its swap). -/
theorem standardBoundaryWord_of_seams (v : Word)
    (hBO : BottomCopyOdd v) (hBE : BottomCopyEven v)
    (hBOs : BottomCopyOdd (swapW v)) (hBEs : BottomCopyEven (swapW v))
    (hCO : CoverNodupOdd v) (hCE : CoverNodupEven v) : StandardBoundaryWord v :=
  ⟨standardBoundaryOdd_of_named v hBO hBEs hCO, standardBoundaryEven_of_named v hBE hBOs hCE⟩

end FLatticePaper.Tiles.SeamFinal
