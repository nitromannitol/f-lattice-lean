import FLatticePaper.Tiles.StandardDischarge
import FLatticePaper.Tiles.PackGap

/-! Task 50, part 2 (Q10): clause (a) of `lemma:standard_tile_properties` from the boundary-word statement alone.

The packing fields `packOdd`, `packEven` of `StandardInputs` (`NoFirstCrossing` and `NoFarAdjacency` of the standard tiles) follow
from the boundary word of the tile (`StandardBoundaryWord`) and the admissibility of the standard words, by
`noFirstCrossing_of_boundary` and `noFarAdjacency_of_boundary` (`Tiles/PackGap.lean`). The simplicity of the tiles is
`simpleOdd_of_standardBoundaryWord`, so clause (a) needs only `StandardBoundaryWord`. -/

namespace FLatticePaper.Tiles.StandardDischarge

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardBoundary FLatticePaper.Tiles.StandardClause FLatticePaper.Tiles.StandardSimple

/-- The letters `i, -1` of a word whose `-i`-image is admissible (the monotone image of `w₂` under `-i`). -/
theorem letters_of_mulNegI_admissible {w : F2Word} (hA : Admissible (w.map Unit4.mulNegI)) :
    ∀ x ∈ w, x = .i ∨ x = .negOne := by
  intro x hx
  have hm := hA.1 x.mulNegI (List.mem_map_of_mem hx)
  have hxe : x = Unit4.mulI (Unit4.mulNegI x) := by cases x <;> rfl
  rcases hm with h | h
  · rw [hxe, h]
    simp [Unit4.mulI]
  · rw [hxe, h]
    simp [Unit4.mulI]

/-- The packing fields of the odd standard tile, from its boundary word and the admissibility of its words. -/
theorem packOdd_of_standardBoundaryWord (bd : ∀ w, StandardBoundaryWord w) (w : Word) :
    NoFirstCrossing (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)) ∧
      NoFarAdjacency (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)) := by
  have hA := admissible_oddStandard w
  have hT := (bd w).1
  have h1 : ∀ x ∈ oddBottom w, x = .one ∨ x = .i := hA.1.1
  have h2 := letters_of_mulNegI_admissible hA.2
  exact ⟨noFirstCrossing_of_boundary hT h1 h2 hA.1 hA.2, noFarAdjacency_of_boundary hT h1 h2 hA.1 hA.2⟩

/-- The packing fields of the even standard tile, from its boundary word and the admissibility of its words. -/
theorem packEven_of_standardBoundaryWord (bd : ∀ w, StandardBoundaryWord w) (w : Word) :
    NoFirstCrossing (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)) ∧
      NoFarAdjacency (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)) := by
  have hA := admissible_evenStandard w
  have hT := (bd w).2
  have h1 : ∀ x ∈ evenBottom w, x = .one ∨ x = .i := hA.1.1
  have h2 := letters_of_mulNegI_admissible hA.2
  exact ⟨noFirstCrossing_of_boundary hT h1 h2 hA.1 hA.2, noFarAdjacency_of_boundary hT h1 h2 hA.1 hA.2⟩

/-- The standard inputs of clause (a) from the boundary-word statement alone (no packing hypothesis). -/
def standardInputsOfBoundary (bd : ∀ w, StandardBoundaryWord w) : StandardInputs :=
  standardInputsDischarged bd (fun w => packOdd_of_standardBoundaryWord bd w)
    (fun w => packEven_of_standardBoundaryWord bd w)

/-- **Clause (a) of `lemma:standard_tile_properties`, odd tiles, from `StandardBoundaryWord` only.** -/
theorem clauseA_standard_odd_of_boundary (bd : ∀ w, StandardBoundaryWord w) (w : Word) :
    IsRegularAlmostTiling (cellTileOf (oddTile w)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) :=
  clauseA_odd (standardInputsOfBoundary bd) w

/-- **Clause (a) of `lemma:standard_tile_properties`, even tiles, from `StandardBoundaryWord` only.** -/
theorem clauseA_standard_even_of_boundary (bd : ∀ w, StandardBoundaryWord w) (w : Word) :
    IsRegularAlmostTiling (cellTileOf (evenTile w)) (texV1Even (fracEven w)) (texV2 (fracEven w)) :=
  clauseA_even (standardInputsOfBoundary bd) w

end FLatticePaper.Tiles.StandardDischarge
