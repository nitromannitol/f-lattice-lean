import FLatticePaper.Tiles.BottomSeam
import FLatticePaper.Tiles.OriginCell
import FLatticePaper.Tiles.SeamSymm

/-! The fields `low` and `symm` of the seam structures `BottomSeamOdd` and `BottomSeamEven` (Q25), for every word.

`low`: the lower-left vertex of the cell tile of the child is the origin (`OriginCell.lowerLeft_origin`).
`symm`: the half-turn symmetry of the boundary of the cell tile about the sum of its bottom and right words
(`SeamSymm.symm_odd`, `SeamSymm.symm_even`). Both are unconditional. -/

namespace FLatticePaper.Tiles.SeamFieldsLowSymm

open FLatticePaper.Farey FLatticePaper.Tiles FLatticePaper.Tiles.Standard FLatticePaper.Tiles.StandardBoundary
  FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.BottomSeam FLatticePaper.Tiles.FourWalks

theorem low_odd (u : Word) : IsLowerLeft (cellTileOf (oddTile u)) (0, 0) :=
  (OriginCell.lowerLeft_origin u).1

theorem low_even (u : Word) : IsLowerLeft (cellTileOf (evenTile u)) (0, 0) :=
  (OriginCell.lowerLeft_origin u).2

theorem symm_odd_field (u : Word) : ∀ e ∈ (cellTileOf (oddTile u)).boundaryEdges,
    halfE (F2Word.sum (oddBottom u) + F2Word.sum (oddRight u)) e ∈ (cellTileOf (oddTile u)).boundaryEdges :=
  SeamSymm.symm_odd u

theorem symm_even_field (u : Word) : ∀ e ∈ (cellTileOf (evenTile u)).boundaryEdges,
    halfE (F2Word.sum (evenBottom u) + F2Word.sum (evenRight u)) e ∈ (cellTileOf (evenTile u)).boundaryEdges :=
  SeamSymm.symm_even u

end FLatticePaper.Tiles.SeamFieldsLowSymm
