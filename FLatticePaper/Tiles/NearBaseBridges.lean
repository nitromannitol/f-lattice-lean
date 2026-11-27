import FLatticePaper.Tiles.StandardTiles
import FLatticePaper.Construction.NearOneBaseCases

/-! # Bridges between the stored near-one base tiles and the paper tiles

The stored standard base tiles `nstairF d` and `nladderF d` (`Tiles/StandardTiles.lean`) are finite filters, and the paper
tiles `paperNearStairTile d` and `paperNearLadderTile d` (`Construction/NearOneBaseCases.lean`) are sets. For `d ≥ 2` the
two agree as vertex sets: the corner points of the paper tile lie in the product box of the filter exactly when `d ≥ 2`. -/

namespace FLatticePaper.Tiles.NearBaseBridges

open FLatticePaper.Tiles.Standard
open FLatticePaper.Construction

/-- The near-one stair: `nstairF d` (before the normalising shift) has the vertex set `paperNearStairTile d`. -/
theorem nstairF_eq_paperNearStairTile {d : ℤ} (hd : 2 ≤ d) :
    ((nstairF d : Finset Site) : Set Site) = paperNearStairTile d := by
  ext ⟨a, b⟩
  simp only [Finset.mem_coe, nstairF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, paperNearStairTile,
    Set.mem_union, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩
    omega
  · intro h
    omega

/-- The near-one ladder: `nladderF d` (before the normalising shift) has the vertex set `paperNearLadderTile d`. -/
theorem nladderF_eq_paperNearLadderTile {d : ℤ} (hd : 2 ≤ d) :
    ((nladderF d : Finset Site) : Set Site) = paperNearLadderTile d := by
  ext ⟨a, b⟩
  simp only [Finset.mem_coe, nladderF, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, paperNearLadderTile,
    Set.mem_sdiff, Set.mem_union, Set.mem_setOf_eq, paperNearLadderA, paperNearLadderB, paperNearLadderC,
    paperNearLadderD, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨_, h⟩
    omega
  · intro h
    omega

end FLatticePaper.Tiles.NearBaseBridges
