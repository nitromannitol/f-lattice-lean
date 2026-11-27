import FLatticePaper.Tiles.GHJoin
import FLatticePaper.Tiles.PseudoSquareAnchored

/-! The join of two forward zero-one strings, with positions.

For a word `X' ++ [p]` ending in `p` and a nonempty word `y :: Y'`, the forward string of `X' ++ [p] ++ (y :: Y')` at `c` is the
forward string of `X' ++ [p]` at `c`, followed by the forward string of `y :: Y'` started at `c + (sum of the step offsets of the
tail of X' ++ [p]) + hOffset y`: the second piece starts one string step after the last tile of the first. The tile types agree
by `tileSeq_append_p`. -/

namespace FLatticePaper.Tiles.StringJoin

open FLatticePaper.Tiles FLatticePaper.Tiles.GHJoin

/-- The positions of a concatenation: those of the first part, then those of the second started at the sum of the first. -/
theorem scanl_add_sum (c : GInt) (A B : List GInt) :
    List.scanl (· + ·) c (A ++ B) =
      List.scanl (· + ·) c A ++ (List.scanl (· + ·) (c + A.sum) B).tail := by
  induction A generalizing c with
  | nil => cases B <;> simp [List.scanl_nil, List.scanl_cons]
  | cons a A ih =>
    simp [List.scanl_cons, ih, List.sum_cons, add_assoc]

/-- The tile sequence has the length of the word. -/
theorem tileSeqAux_length (prev : Option Letter) (w : BinaryWord) :
    (tileSeqAux prev w).length = w.length := by
  induction w generalizing prev with
  | nil => simp [tileSeqAux]
  | cons x w ih =>
    cases x <;> simp [tileSeqAux, ih]

/-- **The join of forward strings, with positions.** -/
theorem hStringAt_join (X' Y' : BinaryWord) (y : Letter) (c : GInt) :
    hStringAt (X' ++ [Letter.p] ++ (y :: Y')) c =
      hStringAt (X' ++ [Letter.p]) c ++
        hStringAt (y :: Y') (c + ((X' ++ [Letter.p]).tail.map hOffset).sum + hOffset y) := by
  have hne : X' ++ [Letter.p] ≠ [] := by simp
  have ht : tileSeq (X' ++ [Letter.p] ++ (y :: Y')) = tileSeq (X' ++ [Letter.p]) ++ tileSeq (y :: Y') := by
    rw [tileSeq_append_p, tileSeqAux_some_p]
    rfl
  have htail : (X' ++ [Letter.p] ++ (y :: Y')).tail = (X' ++ [Letter.p]).tail ++ (y :: Y') :=
    List.tail_append_of_ne_nil hne
  have hlenX : (tileSeq (X' ++ [Letter.p])).length =
      (List.scanl (· + ·) c ((X' ++ [Letter.p]).tail.map hOffset)).length := by
    unfold tileSeq
    rw [tileSeqAux_length, List.length_scanl, List.length_map, List.length_tail]
    have := List.length_pos_of_ne_nil hne
    omega
  have hR : (List.scanl (· + ·) (c + ((X' ++ [Letter.p]).tail.map hOffset).sum)
      ((y :: Y').map hOffset)).tail =
      List.scanl (· + ·) (c + ((X' ++ [Letter.p]).tail.map hOffset).sum + hOffset y) (Y'.map hOffset) := by
    simp [List.map_cons, List.scanl_cons, add_assoc]
  unfold hStringAt
  rw [ht, htail, List.map_append, scanl_add_sum, hR, List.tail_cons]
  rw [List.zip_append hlenX]

end FLatticePaper.Tiles.StringJoin
