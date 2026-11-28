import FLatticePaper.Tiles.LCorrecRecursion

/-! Domains of the actual L pieces in the coordinates of their first stem. The
formulas retain the enlarged square at a pure two prefix and the bridge displacement
at a pure three prefix. Both lengths of the column use the same initial offset. -/

namespace FLatticePaper.Tiles.CorrectedCellsColumn

open FLatticePaper.Farey FLatticePaper.Tiles
open FLatticePaper.Tiles.Standard FLatticePaper.Tiles.JointFamily
open FLatticePaper.Tiles.LCorrecProps FLatticePaper.Tiles.LCorrecRecursion

private theorem pieces_append (ps qs : List Piece) :
    pieceUnion (ps ++ qs) = pieceUnion ps ∪ pieceUnion qs := by
  ext x
  simp only [JointGlue.mem_pieceUnion, Finset.mem_union, List.mem_append]
  aesop

private theorem pieces_range (f : ℕ → Piece) (n : ℕ) :
    pieceUnion ((List.range n).map f) = (Finset.range n).biUnion (fun j => (f j).placed) := by
  ext x
  simp only [JointGlue.mem_pieceUnion, Finset.mem_biUnion, Finset.mem_range, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, hx⟩
    exact ⟨j, hj, hx⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨f j, ⟨j, hj, rfl⟩, hx⟩

private theorem pieces_single (p : Piece) : pieceUnion [p] = p.placed := Finset.union_empty _

private theorem pieces_if (b : Bool) (l r : List Piece) :
    pieceUnion (if b then l else r) = if b then pieceUnion l else pieceUnion r := by cases b <;> rfl

private theorem image_if (b : Bool) (A B : Tile) (v : Site) :
    (if b then A else B).image (· + v) = if b then A.image (· + v) else B.image (· + v) := by cases b <;> rfl

/-- The odd L domain in its initial placement, for arbitrary trailing run length. -/
theorem odd_column (w : Word) (plus elong : Bool) :
    oddLCells w plus elong =
      shift (oddLRel (stripTrailing .two w) (trailingCount .two w) (W1Odd w) plus elong) (oddLInitOff w plus) := by
  simp only [oddLCells, oddLPieces, oddLRel, pieces_append, pieces_range, pieces_single,
    Piece.placed, stdPiece, shift, Finset.image_union, Finset.biUnion_image, img_add,
    stemO, bridgeO, headO]
  simp only [add_comm (oddLInitOff w plus), add_right_comm]

/-- The even L domain in its initial placement, including both choices of the bridge
at a prefix made of twos. -/
theorem even_column (w : Word) (plus elong : Bool) :
    evenLCells w plus elong =
      shift (evenLRel (stripTrailing .three w) (trailingCount .three w) (W1Odd w) plus elong) (evenLInitOff w plus) := by
  simp only [evenLCells, evenLPieces, evenLRel, pieces_append, pieces_range, pieces_if, pieces_single,
    show pieceUnion [] = ∅ from rfl, Piece.placed, stdPiece, enlOdo, shift, Finset.image_union,
    Finset.biUnion_image, image_if, Finset.image_empty, img_add, stemE, bridgeE, headE]
  simp only [add_comm (evenLInitOff w plus), add_right_comm]

end FLatticePaper.Tiles.CorrectedCellsColumn
