import FLatticePaper.Tiles.BottomEdges
import FLatticePaper.Tiles.StandardClauseA
import FLatticePaper.Tiles.AdmissibleStatement

/-! The boundary-word edges of the standard tiles, from the bottom-edge recursion of `BottomEdges.lean` (w3).

For a word `w` the odd tile has bottom edge `oddBottom w` and right edge `oddRight w`; the even tile has `evenBottom w`
and `evenRight w`. The right edge is `i` times the other bottom edge of the rotated word (`swapTwoThree`), as in
`lemma:standard_boundary_word_recursion` Step 2 (`T(R(n/d))` has boundary word `(-i w2, -i w1)`). The sums are the
lattice vectors of clause (a): `almostV₁ = Σ w1 + i`, `almostV₂ = Σ w2 - 1`. -/

namespace FLatticePaper.Tiles.StandardBoundary

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles
open FLatticePaper.Tiles.StandardClause

/-- The bottom edge of the odd tile of `w`. -/
def oddBottom (w : Word) : F2Word := (bottomEdges w).1

/-- The right edge of the odd tile of `w`: `i` times the even bottom edge of the rotated word. -/
def oddRight (w : Word) : F2Word := ((bottomEdges (w.map Digit.swapTwoThree)).2).map Unit4.mulI

/-- The bottom edge of the even tile of `w`. -/
def evenBottom (w : Word) : F2Word := (bottomEdges w).2

/-- The right edge of the even tile of `w`: `i` times the odd bottom edge of the rotated word. -/
def evenRight (w : Word) : F2Word := ((bottomEdges (w.map Digit.swapTwoThree)).1).map Unit4.mulI

/-- The sum of the bottom edge of the odd tile plus `i` is the odd lattice vector (w3, `bottomEdges_odd_sum`). -/
theorem sum_oddBottom (w : Word) : almostV₁ (oddBottom w) = texV1Odd (fracOdd w) :=
  bottomEdges_odd_sum w

/-- The sum of the bottom edge of the even tile plus `i` is the even lattice vector (w3, `bottomEdges_even_sum`). -/
theorem sum_evenBottom (w : Word) : almostV₁ (evenBottom w) = texV1Even (fracEven w) :=
  bottomEdges_even_sum w

/-- The sum of the right edge of the even tile minus `1` is `texV2` of the even fraction (w3, `bottomEdges_second_sum`). -/
theorem sum_evenRight (w : Word) : almostV₂ (evenRight w) = texV2 (fracEven w) :=
  bottomEdges_second_sum w

/-- The sum of the right edge of the odd tile minus `1` is `texV2` of the odd fraction. The rotation identities of
`BottomEdges.lean` give it from the even bottom edge of the rotated word. -/
theorem sum_oddRight (w : Word) : almostV₂ (oddRight w) = texV2 (fracOdd w) := by
  have hE := bottomEdges_even_sum (w.map Digit.swapTwoThree)
  rw [parentsAt_swap_eq] at hE
  have hV := parentsAt_valid w
  have he : (parentsAt w).even.Even := hV.even_parity
  have ho : (parentsAt w).odd.Odd := hV.odd_parity
  have hsum := eq_sub_of_add_eq hE
  unfold almostV₂ oddRight fracOdd
  rw [F2Word_sum_map_mulI, hsum, rotI_sub]
  have hgI : rotI gI = -gOne := by
    simp [rotI, gI, gOne]
  rw [hgI]
  rw [Fraction.rotate_of_even he, Fraction.rotate_of_odd ho]
  have he' : ((parentsAt w).even.num + (parentsAt w).even.den) % 2 = 0 := he
  apply Prod.ext
  · simp [rotI, gOne, texV1Even, texV2, Parents.current, Parents.combine]
    omega
  · simp [rotI, gOne, texV1Even, texV2, Parents.current, Parents.combine]
    omega

end FLatticePaper.Tiles.StandardBoundary

namespace FLatticePaper.Tiles.StandardBoundary

open FLatticePaper FLatticePaper.Farey FLatticePaper.Construction FLatticePaper.Tiles FLatticePaper.Tiles.Standard
open FLatticePaper.Tiles.StandardClause

/-- The boundary-word statement of the odd tile of `w` (part 2 of `lemma:standard_boundary_word_recursion`): the cell
tile of `oddTile w` has boundary word `w1 * w2 * hat(rev w1) * hat(rev w2)` from its lower-left vertex `(0,0)`, with
`w1 = oddBottom w` and `w2 = oddRight w`. -/
def StandardBoundaryOdd (w : Word) : Prop :=
  IsBoundaryWordAt (cellTileOf (oddTile w)) (0, 0) (boundaryWordOf (oddBottom w) (oddRight w))

/-- The boundary-word statement of the even tile of `w`, with `w1 = evenBottom w`, `w2 = evenRight w`. -/
def StandardBoundaryEven (w : Word) : Prop :=
  IsBoundaryWordAt (cellTileOf (evenTile w)) (0, 0) (boundaryWordOf (evenBottom w) (evenRight w))

/-- `StandardBoundaryWord w`: both tiles of `w` have the boundary-word form (the input `StandardBoundaryWord`). -/
def StandardBoundaryWord (w : Word) : Prop := StandardBoundaryOdd w ∧ StandardBoundaryEven w

/-- The admissibility of the odd standard tile's words: `w1 = oddBottom w` and `-i w2 = (bottomEdges (swap w)).2`
(`bottomEdges_admissible`, task 51). -/
theorem admissible_oddStandard (w : Word) :
    Admissible (oddBottom w) ∧ Admissible ((oddRight w).map Unit4.mulNegI) := by
  refine ⟨(bottomEdges_admissible w).1, ?_⟩
  unfold oddRight
  rw [mulNegI_mulI_list]
  exact (bottomEdges_admissible _).2

/-- The admissibility of the even standard tile's words: `w1 = evenBottom w` and `-i w2 = (bottomEdges (swap w)).1`. -/
theorem admissible_evenStandard (w : Word) :
    Admissible (evenBottom w) ∧ Admissible ((evenRight w).map Unit4.mulNegI) := by
  refine ⟨(bottomEdges_admissible w).2, ?_⟩
  unfold evenRight
  rw [mulNegI_mulI_list]
  exact (bottomEdges_admissible _).1

/-- The standard inputs of clause (a), with the lattice sums discharged by w3's theorems and the rotation identities
(`sum_oddBottom`, `sum_oddRight`, `sum_evenBottom`, `sum_evenRight`) and the admissibility discharged by
`bottomEdges_admissible` (`admissible_oddStandard`, `admissible_evenStandard`). The remaining inputs are the simplicity
of the tiles and the packing hypothesis. -/
def standardInputsOf (bd : ∀ w, StandardBoundaryWord w)
    (simpleO : ∀ w, IsSimpleTile (cellTileOf (oddTile w)))
    (simpleE : ∀ w, IsSimpleTile (cellTileOf (evenTile w)))
    (packO : ∀ w, NoFirstCrossing (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)) ∧
      NoFarAdjacency (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)))
    (packE : ∀ w, NoFirstCrossing (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)) ∧
      NoFarAdjacency (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w))) :
    StandardInputs where
  W1 := oddBottom
  W2 := oddRight
  V1 := evenBottom
  V2 := evenRight
  bdOdd := fun w => (bd w).1
  bdEven := fun w => (bd w).2
  sumOdd := fun w => ⟨sum_oddBottom w, sum_oddRight w⟩
  sumEven := fun w => ⟨sum_evenBottom w, sum_evenRight w⟩
  admOdd := admissible_oddStandard
  admEven := admissible_evenStandard
  simpleOdd := simpleO
  simpleEven := simpleE
  packOdd := packO
  packEven := packE

/-- Clause (a) for the odd tile of every word, from the boundary-word input, the simplicity and packing inputs (the
admissibility is discharged by `bottomEdges_admissible`). -/
theorem clauseA_standard_odd (bd : ∀ w, StandardBoundaryWord w)
    (simpleO : ∀ w, IsSimpleTile (cellTileOf (oddTile w)))
    (simpleE : ∀ w, IsSimpleTile (cellTileOf (evenTile w)))
    (packO : ∀ w, NoFirstCrossing (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)) ∧
      NoFarAdjacency (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)))
    (packE : ∀ w, NoFirstCrossing (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)) ∧
      NoFarAdjacency (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)))
    (w : Word) :
    IsRegularAlmostTiling (cellTileOf (oddTile w)) (texV1Odd (fracOdd w)) (texV2 (fracOdd w)) :=
  clauseA_odd (standardInputsOf bd simpleO simpleE packO packE) w

/-- Clause (a) for the even tile of every word. -/
theorem clauseA_standard_even (bd : ∀ w, StandardBoundaryWord w)
    (simpleO : ∀ w, IsSimpleTile (cellTileOf (oddTile w)))
    (simpleE : ∀ w, IsSimpleTile (cellTileOf (evenTile w)))
    (packO : ∀ w, NoFirstCrossing (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)) ∧
      NoFarAdjacency (cellTileOf (oddTile w)) (almostV₁ (oddBottom w)) (almostV₂ (oddRight w)))
    (packE : ∀ w, NoFirstCrossing (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)) ∧
      NoFarAdjacency (cellTileOf (evenTile w)) (almostV₁ (evenBottom w)) (almostV₂ (evenRight w)))
    (w : Word) :
    IsRegularAlmostTiling (cellTileOf (evenTile w)) (texV1Even (fracEven w)) (texV2 (fracEven w)) :=
  clauseA_even (standardInputsOf bd simpleO simpleE packO packE) w

end FLatticePaper.Tiles.StandardBoundary
