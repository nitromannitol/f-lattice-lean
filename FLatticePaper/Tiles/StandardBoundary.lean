import FLatticePaper.Tiles.BottomEdges
import FLatticePaper.Tiles.StandardClauseA

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
