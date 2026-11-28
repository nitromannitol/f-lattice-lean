import FLatticePaper.Tiles.CorrectedCellsColumn

/-! The last head of an elongated L in the coordinates of the enclosing tile. -/

namespace FLatticePaper.Tiles.CorrectedCellsEnds

open FLatticePaper.Farey FLatticePaper.Tiles
open Standard JointFamily LCorrecProps LCorrecRecursion

private theorem last_union (k : ℕ) (f : ℕ → Tile) :
    (Finset.range (2*(k+1))).biUnion f =
      (Finset.range (2*(k+1)-1)).biUnion f ∪ f (2*(k+1)-1) := by
  conv_lhs => rw [show 2*(k+1) = (2*(k+1)-1)+1 by omega, Finset.range_add_one, Finset.biUnion_insert]
  exact Finset.union_comm _ _

/-- The coefficient of the last head relative to the first stem. -/
def endCoeff (k : ℕ) (K : SurgicalAlt.AltCoeff × SurgicalAlt.AltCoeff × SurgicalAlt.AltCoeff × SurgicalAlt.AltCoeff) :
    SurgicalAlt.AltCoeff :=
  (k : ℤ) • K.1 + K.2.1 + K.2.2.1 + (2*((k : ℤ)+1)) • K.2.2.2

/-- Elongating an even L adds one translate of its alternate odd register, for both signs and every prefix. -/
theorem even_long (w : Word) (plus : Bool) :
    let pre := stripTrailing .three w
    let k := trailingCount .three w
    let K := evenKCoeff (W1Odd w) plus (decide (pre.getLast? = some Digit.two))
    evenLCells w plus true = evenLCells w plus false ∪
      shift (headE pre) (altOff pre (endCoeff k K) + evenLInitOff w plus) := by
  dsimp only
  rw [CorrectedCellsColumn.even_column, CorrectedCellsColumn.even_column]
  simp only [evenLRel, if_true, Bool.false_eq_true, if_false, Nat.sub_zero]
  rw [last_union]
  have hc (k : ℕ) : ((2*(k+1)-1 : ℕ) : ℤ) + 1 = 2*((k : ℤ)+1) := by omega
  rw [hc]
  simp only [shift, Finset.image_union, img_add, endCoeff]
  ac_rfl

/-- Elongating an odd L adds one translate of its alternate even register, including at a shifted bridge. -/
theorem odd_long (w : Word) (plus : Bool) :
    let pre := stripTrailing .two w
    let k := trailingCount .two w
    let K := oddKCoeff (W1Odd w) plus
    oddLCells w plus true = oddLCells w plus false ∪
      shift (headO pre) (altOff pre (endCoeff k K) + oddLInitOff w plus) := by
  dsimp only
  rw [CorrectedCellsColumn.odd_column, CorrectedCellsColumn.odd_column]
  simp only [oddLRel, if_true, Bool.false_eq_true, if_false, Nat.sub_zero]
  rw [last_union]
  have hc (k : ℕ) : ((2*(k+1)-1 : ℕ) : ℤ) + 1 = 2*((k : ℤ)+1) := by omega
  rw [hc]
  simp only [shift, Finset.image_union, img_add, endCoeff]
  ac_rfl

end FLatticePaper.Tiles.CorrectedCellsEnds
