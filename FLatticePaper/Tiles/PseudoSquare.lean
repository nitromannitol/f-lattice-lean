import FLatticePaper.Tiles.AlmostTiling
import FLatticePaper.Tiles.BoundaryStrings

namespace FLatticePaper.Tiles

/-! Pseudo-square tiles and boundary words (paper Section 5.6, lines 1617-1704). The combinatorial maps
`G` and `R` and the boundary-word shape are formalized here; the geometric identities of Table 1 (line 1697) enter
only as explicit hypotheses in `IsPseudoSquare`. -/

/-- The zero-one tile types of a horizontal string (lines 1262-1282 and 1273-1276). `zero` is `T_{0/1}` (letter `p`),
`one` is `T_{1/1}` (letter `q`), and `oneD` is the enlarged `T^d_{1/1}` that replaces a `q` following a `q`. -/
inductive ZTile
  | zero
  | one
  | oneD
  deriving DecidableEq, Repr

/-- The doubled tile sequence, read left to right with the previous letter: `p` gives `zero`; `q` gives `oneD` after a
`q` and `one` otherwise (lines 1273-1276). -/
def tileSeqAux : Option Letter → BinaryWord → List ZTile
  | _, [] => []
  | prev, x :: xs =>
    (match x, prev with
      | .p, _ => ZTile.zero
      | .q, some .q => ZTile.oneD
      | .q, _ => ZTile.one) :: tileSeqAux (some x) xs

/-- The tile sequence of a horizontal word (lines 1273-1276): the doubling rule `q q ↦ q q_d` applied to the letters
of the word. The reading of the rule on runs `qqq` is the one stated here. -/
def tileSeq (w : BinaryWord) : List ZTile := tileSeqAux none w

/-- `g` on a pair of consecutive tiles (eq:g_boundary_word_pairwise, lines 1647-1663). The three pairs that cannot
occur in a tile sequence are sent to the empty word. -/
def gPair : ZTile → ZTile → F2Word
  | .zero, .one => [Unit4.one, Unit4.i]
  | .one, .zero => [Unit4.one, Unit4.one]
  | .oneD, .zero => [Unit4.i, Unit4.one]
  | .zero, .zero => [Unit4.one, Unit4.one]
  | .one, .oneD => [Unit4.one, Unit4.one]
  | .oneD, .oneD => [Unit4.i, Unit4.one]
  | _, _ => []

/-- `G` on a horizontal word (eq:g_boundary_word_w_h, line 1666): `g` on the consecutive pairs of the tile sequence,
then the final `* 1`. -/
def gH (w : BinaryWord) : F2Word :=
  let ts := tileSeq w
  ((ts.zip ts.tail).flatMap fun ab => gPair ab.1 ab.2) ++ [Unit4.one]

/-- The flip `F` of a letter (line 1636: `F` flips every `p` to a `q` and conversely). -/
def flipLetter : Letter → Letter
  | .p => .q
  | .q => .p

/-- The flip `F(w)` of a word. -/
def flipW (w : BinaryWord) : BinaryWord := w.map flipLetter

/-- `G(w_v) = i · G(F(w_v))` (line 1670), with `i ·` acting letterwise. -/
def gV (w : BinaryWord) : F2Word := (gH (flipW w)).map Unit4.mulI

/-- `G(w_h, w_v) = (G(w_h), G(w_v))` (line 1671). -/
def gPseudo (wh wv : BinaryWord) : F2Word × F2Word := (gH wh, gV wv)

/-- The rotation `R(w_h, w_v) = (F(w_v), F(w_h))` of a pair of strings (eq:rotate_boundary_string, line 1645). -/
def rotPseudo (wh wv : BinaryWord) : BinaryWord × BinaryWord := (flipW wv, flipW wh)

/-- The boundary word shape `w_1 * w_2 * hat(rev w_1) * hat(rev w_2)` of the lemma at line 1686. -/
def pseudoBoundaryWord (w1 w2 : F2Word) : F2Word :=
  w1 ++ w2 ++ F2Word.hat (F2Word.rev w1) ++ F2Word.hat (F2Word.rev w2)

/-! ### Letter identities -/

theorem Unit4.neg_mulI (x : Unit4) : x.mulI.neg = x.mulNegI := by
  cases x <;> rfl

theorem Unit4.neg_mulNegI (x : Unit4) : x.mulNegI.neg = x.mulI := by
  cases x <;> rfl

theorem Unit4.mulI_mulNegI (x : Unit4) : x.mulNegI.mulI = x := by
  cases x <;> rfl

theorem Unit4.mulNegI_mulI (x : Unit4) : x.mulI.mulNegI = x := by
  cases x <;> rfl

theorem Unit4.neg_neg' (x : Unit4) : x.neg.neg = x := by
  cases x <;> rfl

/-- `hat (rev w)` is the letterwise negation of `w` (the half-turn of the string, lines 1645-1698). -/
theorem hat_rev_eq_map_neg (w : F2Word) : F2Word.hat (F2Word.rev w) = w.map Unit4.neg := by
  simp [F2Word.hat, F2Word.rev, List.map_reverse]

theorem Unit4.mulI_neg (x : Unit4) : x.neg.mulI = x.mulNegI := by
  cases x <;> rfl

theorem Letter.flip_flip (x : Letter) : flipLetter (flipLetter x) = x := by
  cases x <;> rfl

theorem flipW_flipW (w : BinaryWord) : flipW (flipW w) = w := by
  simp [flipW, List.map_map, Function.comp_def, Letter.flip_flip]

theorem map_mulI_mulNegI (l : F2Word) : (l.map Unit4.mulI).map Unit4.mulNegI = l := by
  simp [List.map_map, Function.comp_def, Unit4.mulNegI_mulI]

/-! ### The half-turn and the quarter-turn of the boundary word -/

/-- The boundary word of a pseudo-square is invariant under the half-turn: negating every letter and rotating by
half the length gives the same word (line 1698, "180-degree symmetric"). -/
theorem pseudoBoundaryWord_halfTurn (w1 w2 : F2Word) :
    (pseudoBoundaryWord w1 w2).map Unit4.neg =
      (pseudoBoundaryWord w1 w2).rotate (w1.length + w2.length) := by
  unfold pseudoBoundaryWord
  simp only [hat_rev_eq_map_neg, List.map_append, List.map_map, Function.comp_def, Unit4.neg_neg']
  have hsplit : w1 ++ w2 ++ w1.map Unit4.neg ++ w2.map Unit4.neg =
      (w1 ++ w2) ++ (w1.map Unit4.neg ++ w2.map Unit4.neg) := by
    simp [List.append_assoc]
  have hlen : w1.length + w2.length = (w1 ++ w2).length := by simp
  rw [hsplit, hlen, List.rotate_append_length_eq]
  simp [List.append_assoc]

/-- The boundary word of the rotated pair is the quarter-turn of the boundary word: the first and second words become
`-i w_2` and `i w_1`, and the boundary word is a rotation of `i` times the original (line 1698, "R(T) is a 90-degree
rotation of T"). -/
theorem pseudoBoundaryWord_rotation (w1 w2 : F2Word) :
    pseudoBoundaryWord (w2.map Unit4.mulNegI) (w1.map Unit4.mulI) =
      ((pseudoBoundaryWord w1 w2).map Unit4.mulI).rotate (w1.length + w2.length + w1.length) := by
  have hL : pseudoBoundaryWord (w2.map Unit4.mulNegI) (w1.map Unit4.mulI) =
      w2.map Unit4.mulNegI ++ w1.map Unit4.mulI ++ w2.map Unit4.mulI ++ w1.map Unit4.mulNegI := by
    unfold pseudoBoundaryWord
    simp only [hat_rev_eq_map_neg, List.map_map, Function.comp_def, Unit4.neg_mulNegI, Unit4.neg_mulI]
  have hW : (pseudoBoundaryWord w1 w2).map Unit4.mulI =
      (w1.map Unit4.mulI ++ w2.map Unit4.mulI ++ w1.map Unit4.mulNegI) ++ w2.map Unit4.mulNegI := by
    unfold pseudoBoundaryWord
    simp only [hat_rev_eq_map_neg, List.map_append, List.map_map, Function.comp_def, Unit4.mulI_neg]
  have hlen : (w1.map Unit4.mulI ++ w2.map Unit4.mulI ++ w1.map Unit4.mulNegI).length =
      w1.length + w2.length + w1.length := by
    simp; omega
  rw [hL, hW, ← hlen, List.rotate_append_length_eq]
  simp [List.append_assoc]

/-- `G` of the rotated pair: `G(R(w_h, w_v)) = (-i · G(w_v), i · G(w_h))`. -/
theorem gPseudo_rotPseudo (wh wv : BinaryWord) :
    gPseudo (rotPseudo wh wv).1 (rotPseudo wh wv).2 =
      ((gPseudo wh wv).2.map Unit4.mulNegI, (gPseudo wh wv).1.map Unit4.mulI) := by
  refine Prod.ext ?_ ?_
  · show gH (flipW wv) = (gV wv).map Unit4.mulNegI
    unfold gV
    rw [map_mulI_mulNegI]
  · show gV (flipW wh) = (gH wh).map Unit4.mulI
    unfold gV
    rw [flipW_flipW]

/-! ### Pseudo-squares and the boundary-word lemma -/

/-- A `(w_h, w_v)`-pseudo-square (Definition def:tile_boundary_strings, lines 1626-1633). The boundary of `T`, read
counterclockwise from a lower-left vertex `c`, is the concatenation of four traces: the lower trace `lo` and the right
trace `ri` of the two zero-one strings, and the upper and left traces, which are the half-turns of the reversed strings
(line 1698). The Table 1 identities `lo = G(w_h)` and `ri = G(w_v)` (line 1697, "by checking Table 1 and the figures")
are geometric, so they are explicit fields here, not proved. The subtile decomposition is not formalized. -/
structure IsPseudoSquare (T : CellTile) (wh wv : BinaryWord) : Prop where
  trace : ∃ c : GInt, ∃ lo ri : F2Word,
    IsBoundaryWordAt T c (lo ++ ri ++ F2Word.hat (F2Word.rev lo) ++ F2Word.hat (F2Word.rev ri)) ∧
      lo = (gPseudo wh wv).1 ∧ ri = (gPseudo wh wv).2

/-- The boundary-word lemma (line 1686): the boundary word of a `(w_h, w_v)`-pseudo-square is
`w_1 * w_2 * hat(rev w_1) * hat(rev w_2)` with `(w_1, w_2) = G(w_h, w_v)`. The proof is the assembly of the four traces
from the Table 1 fields of `IsPseudoSquare`. -/
theorem pseudoSquare_boundaryWord {T : CellTile} {wh wv : BinaryWord} (hT : IsPseudoSquare T wh wv) :
    IsBoundaryWord T (pseudoBoundaryWord (gPseudo wh wv).1 (gPseudo wh wv).2) := by
  obtain ⟨c, lo, ri, hb, hlo, hri⟩ := hT.trace
  refine ⟨c, ?_⟩
  rw [← hlo, ← hri]
  exact hb

/-- "In particular, `T` is 180-degree symmetric" (line 1686): the boundary word of a pseudo-square is a boundary word
and is invariant under the half-turn, which negates the letters and rotates by half the length. -/
theorem pseudoSquare_halfTurn {T : CellTile} {wh wv : BinaryWord} (hT : IsPseudoSquare T wh wv) :
    IsBoundaryWord T (pseudoBoundaryWord (gPseudo wh wv).1 (gPseudo wh wv).2) ∧
      (pseudoBoundaryWord (gPseudo wh wv).1 (gPseudo wh wv).2).map Unit4.neg =
        (pseudoBoundaryWord (gPseudo wh wv).1 (gPseudo wh wv).2).rotate
          ((gPseudo wh wv).1.length + (gPseudo wh wv).2.length) :=
  ⟨pseudoSquare_boundaryWord hT, pseudoBoundaryWord_halfTurn _ _⟩

/-- "In particular, `R(T)` is a 90-degree rotation of `T`" (line 1686): the boundary word of the rotated pair is a
rotation of the `i`-multiple of the boundary word of `T`. -/
theorem pseudoSquare_quarterTurn (wh wv : BinaryWord) :
    pseudoBoundaryWord (gPseudo (rotPseudo wh wv).1 (rotPseudo wh wv).2).1
        (gPseudo (rotPseudo wh wv).1 (rotPseudo wh wv).2).2 =
      ((pseudoBoundaryWord (gPseudo wh wv).1 (gPseudo wh wv).2).map Unit4.mulI).rotate
        ((gPseudo wh wv).1.length + (gPseudo wh wv).2.length + (gPseudo wh wv).1.length) := by
  rw [gPseudo_rotPseudo]
  exact pseudoBoundaryWord_rotation _ _

end FLatticePaper.Tiles
